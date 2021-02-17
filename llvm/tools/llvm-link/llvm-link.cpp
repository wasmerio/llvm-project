//===- llvm-link.cpp - Low-level LLVM linker ------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This utility may be invoked in the following manner:
//  llvm-link a.bc b.bc c.bc -o x.bc
//
//===----------------------------------------------------------------------===//

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/BinaryFormat/Magic.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/IR/AutoUpgrade.h"
#include "llvm/IR/DiagnosticInfo.h"
#include "llvm/IR/DiagnosticPrinter.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/ModuleSummaryIndex.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Linker/Linker.h"
#include "llvm/Object/Archive.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/Mutex.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/SystemUtils.h"
#include "llvm/Support/ThreadPool.h"
#include "llvm/Support/Threading.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/WithColor.h"
#include "llvm/Transforms/IPO/FunctionImport.h"
#include "llvm/Transforms/IPO/Internalize.h"
#include "llvm/Transforms/Utils/FunctionImportUtils.h"

#include <memory>
#include <utility>
using namespace llvm;

static cl::list<std::string>
InputFilenames(cl::Positional, cl::OneOrMore,
               cl::desc("<input bitcode files>"));

static cl::list<std::string> OverridingInputs(
    "override", cl::ZeroOrMore, cl::value_desc("filename"),
    cl::desc(
        "input bitcode file which can override previously defined symbol(s)"));

// Option to simulate function importing for testing. This enables using
// llvm-link to simulate ThinLTO backend processes.
static cl::list<std::string> Imports(
    "import", cl::ZeroOrMore, cl::value_desc("function:filename"),
    cl::desc("Pair of function name and filename, where function should be "
             "imported from bitcode in filename"));

// Option to support testing of function importing. The module summary
// must be specified in the case were we request imports via the -import
// option, as well as when compiling any module with functions that may be
// exported (imported by a different llvm-link -import invocation), to ensure
// consistent promotion and renaming of locals.
static cl::opt<std::string>
    SummaryIndex("summary-index", cl::desc("Module summary index filename"),
                 cl::init(""), cl::value_desc("filename"));

static cl::opt<std::string>
OutputFilename("o", cl::desc("Override output filename"), cl::init("-"),
               cl::value_desc("filename"));

static cl::opt<bool>
Internalize("internalize", cl::desc("Internalize linked symbols"));

static cl::opt<bool>
    DisableDITypeMap("disable-debug-info-type-map",
                     cl::desc("Don't use a uniquing type map for debug info"));

static cl::opt<bool>
OnlyNeeded("only-needed", cl::desc("Link only needed symbols"));

static cl::opt<bool>
Force("f", cl::desc("Enable binary output on terminals"));

static cl::opt<bool>
    DisableLazyLoad("disable-lazy-loading",
                    cl::desc("Disable lazy module loading"));

static cl::opt<bool>
    OutputAssembly("S", cl::desc("Write output as LLVM assembly"), cl::Hidden);

static cl::opt<bool>
Verbose("v", cl::desc("Print information about actions taken"));

static cl::opt<bool>
DumpAsm("d", cl::desc("Print assembly as linked"), cl::Hidden);

static cl::opt<bool>
SuppressWarnings("suppress-warnings", cl::desc("Suppress all linking warnings"),
                 cl::init(false));

static cl::opt<bool> PreserveBitcodeUseListOrder(
    "preserve-bc-uselistorder",
    cl::desc("Preserve use-list order when writing LLVM bitcode."),
    cl::init(true), cl::Hidden);

static cl::opt<bool> PreserveAssemblyUseListOrder(
    "preserve-ll-uselistorder",
    cl::desc("Preserve use-list order when writing LLVM assembly."),
    cl::init(false), cl::Hidden);

static cl::opt<bool> NoVerify("disable-verify",
                              cl::desc("Do not run the verifier"), cl::Hidden);

static cl::opt<bool>
ContextEachInput("context-each-input",
                 cl::desc("Use a different LLVMContext for each input file "
                          "(default: for each thread)"),
                 cl::init(false));

static cl::opt<bool> NumThreads(
    "num-threads", cl::init(1),
    cl::desc("Number of load threads to use "
             "(default: 1, use 0 for autodetect)"));

static cl::alias NumThreadsA("j", cl::desc("Alias for --num-threads"),
    cl::aliasopt(NumThreads));

static ExitOnError ExitOnErr;

// Read the specified bitcode file in and return it. This routine searches the
// link path for the specified file to try to find it...
//
static std::unique_ptr<Module> loadFile(const char *argv0,
                                        std::unique_ptr<MemoryBuffer> Buffer,
                                        LLVMContext &Context,
                                        bool MaterializeMetadata = true) {
  SMDiagnostic Err;
  if (Verbose)
    errs() << "Loading '" << Buffer->getBufferIdentifier() << "'\n";
  std::unique_ptr<Module> Result;
  if (DisableLazyLoad)
    Result = parseIR(*Buffer, Err, Context);
  else
    Result =
        getLazyIRModule(std::move(Buffer), Err, Context, !MaterializeMetadata);

  if (!Result) {
    Err.print(argv0, errs());
    return nullptr;
  }

  if (MaterializeMetadata) {
    ExitOnErr(Result->materializeMetadata());
    UpgradeDebugInfo(*Result);
  }

  return Result;
}

static std::unique_ptr<Module> loadArFile(const char *Argv0,
                                          std::unique_ptr<MemoryBuffer> Buffer,
                                          LLVMContext &Context) {
  std::unique_ptr<Module> Result(new Module("ArchiveModule", Context));
  StringRef ArchiveName = Buffer->getBufferIdentifier();
  if (Verbose)
    errs() << "Reading library archive file '" << ArchiveName
           << "' to memory\n";
  Error Err = Error::success();
  object::Archive Archive(*Buffer, Err);
  ExitOnErr(std::move(Err));
  Linker L(*Result);
  for (const object::Archive::Child &C : Archive.children(Err)) {
    Expected<StringRef> Ename = C.getName();
    if (Error E = Ename.takeError()) {
      errs() << Argv0 << ": ";
      WithColor::error()
          << " failed to read name of archive member"
          << ArchiveName << "'\n";
      return nullptr;
    }
    std::string ChildName = Ename.get().str();
    if (Verbose)
      errs() << "Parsing member '" << ChildName
             << "' of archive library to module.\n";
    SMDiagnostic ParseErr;
    Expected<MemoryBufferRef> MemBuf = C.getMemoryBufferRef();
    if (Error E = MemBuf.takeError()) {
      errs() << Argv0 << ": ";
      WithColor::error() << " loading memory for member '" << ChildName
                         << "' of archive library failed'" << ArchiveName
                         << "'\n";
      return nullptr;
    };

    if (!isBitcode(reinterpret_cast<const unsigned char *>
                   (MemBuf.get().getBufferStart()),
                   reinterpret_cast<const unsigned char *>
                   (MemBuf.get().getBufferEnd()))) {
      errs() << Argv0 << ": ";
      WithColor::error() << "  member of archive is not a bitcode file: '"
                         << ChildName << "'\n";
      return nullptr;
    }

    std::unique_ptr<Module> M;
    if (DisableLazyLoad)
      M = parseIR(MemBuf.get(), ParseErr, Context);
    else
      M = getLazyIRModule(MemoryBuffer::getMemBuffer(MemBuf.get(), false),
                          ParseErr, Context);

    if (!M.get()) {
      errs() << Argv0 << ": ";
      WithColor::error() << " parsing member '" << ChildName
                         << "' of archive library failed'" << ArchiveName
                         << "'\n";
      return nullptr;
    }
    if (Verbose)
      errs() << "Linking member '" << ChildName << "' of archive library.\n";
    if (L.linkInModule(std::move(M)))
      return nullptr;
  } // end for each child
  ExitOnErr(std::move(Err));
  return Result;
}

namespace {

/// Helper to load on demand a Module from file and cache it for subsequent
/// queries during function importing.
class ModuleLazyLoaderCache {
  /// Cache of lazily loaded module for import.
  StringMap<std::unique_ptr<Module>> ModuleMap;

  /// Retrieve a Module from the cache or lazily load it on demand.
  std::function<std::unique_ptr<Module>(const char *argv0,
                                        const std::string &FileName)>
      createLazyModule;

public:
  /// Create the loader, Module will be initialized in \p Context.
  ModuleLazyLoaderCache(std::function<std::unique_ptr<Module>(
                            const char *argv0, const std::string &FileName)>
                            createLazyModule)
      : createLazyModule(std::move(createLazyModule)) {}

  /// Retrieve a Module from the cache or lazily load it on demand.
  Module &operator()(const char *argv0, const std::string &FileName);

  std::unique_ptr<Module> takeModule(const std::string &FileName) {
    auto I = ModuleMap.find(FileName);
    assert(I != ModuleMap.end());
    std::unique_ptr<Module> Ret = std::move(I->second);
    ModuleMap.erase(I);
    return Ret;
  }
};

// Get a Module for \p FileName from the cache, or load it lazily.
Module &ModuleLazyLoaderCache::operator()(const char *argv0,
                                          const std::string &Identifier) {
  auto &Module = ModuleMap[Identifier];
  if (!Module) {
    Module = createLazyModule(argv0, Identifier);
    assert(Module && "Failed to create lazy module!");
  }
  return *Module;
}
} // anonymous namespace

namespace {
struct LLVMLinkDiagnosticHandler : public DiagnosticHandler {
  bool handleDiagnostics(const DiagnosticInfo &DI) override {
    unsigned Severity = DI.getSeverity();
    switch (Severity) {
    case DS_Error:
      WithColor::error();
      break;
    case DS_Warning:
      if (SuppressWarnings)
        return true;
      WithColor::warning();
      break;
    case DS_Remark:
    case DS_Note:
      llvm_unreachable("Only expecting warnings and errors");
    }

    DiagnosticPrinterRawOStream DP(errs());
    DI.print(DP);
    errs() << '\n';
    return true;
  }
};
}

/// Import any functions requested via the -import option.
static bool importFunctions(const char *argv0, Module &DestModule) {
  if (SummaryIndex.empty())
    return true;
  std::unique_ptr<ModuleSummaryIndex> Index =
      ExitOnErr(llvm::getModuleSummaryIndexForFile(SummaryIndex));

  // Map of Module -> List of globals to import from the Module
  FunctionImporter::ImportMapTy ImportList;

  auto ModuleLoader = [&DestModule](const char *argv0,
                                    const std::string &Identifier) {
    std::unique_ptr<MemoryBuffer> Buffer =
        ExitOnErr(errorOrToExpected(MemoryBuffer::getFileOrSTDIN(Identifier)));
    return loadFile(argv0, std::move(Buffer), DestModule.getContext(), false);
  };

  ModuleLazyLoaderCache ModuleLoaderCache(ModuleLoader);
  for (const auto &Import : Imports) {
    // Identify the requested function and its bitcode source file.
    size_t Idx = Import.find(':');
    if (Idx == std::string::npos) {
      errs() << "Import parameter bad format: " << Import << "\n";
      return false;
    }
    std::string FunctionName = Import.substr(0, Idx);
    std::string FileName = Import.substr(Idx + 1, std::string::npos);

    // Load the specified source module.
    auto &SrcModule = ModuleLoaderCache(argv0, FileName);

    if (!NoVerify && verifyModule(SrcModule, &errs())) {
      errs() << argv0 << ": " << FileName;
      WithColor::error() << "input module is broken!\n";
      return false;
    }

    Function *F = SrcModule.getFunction(FunctionName);
    if (!F) {
      errs() << "Ignoring import request for non-existent function "
             << FunctionName << " from " << FileName << "\n";
      continue;
    }
    // We cannot import weak_any functions without possibly affecting the
    // order they are seen and selected by the linker, changing program
    // semantics.
    if (F->hasWeakAnyLinkage()) {
      errs() << "Ignoring import request for weak-any function " << FunctionName
             << " from " << FileName << "\n";
      continue;
    }

    if (Verbose)
      errs() << "Importing " << FunctionName << " from " << FileName << "\n";

    auto &Entry = ImportList[FileName];
    Entry.insert(F->getGUID());
  }
  auto CachedModuleLoader = [&](StringRef Identifier) {
    return ModuleLoaderCache.takeModule(std::string(Identifier));
  };
  FunctionImporter Importer(*Index, CachedModuleLoader,
                            /*ClearDSOLocalOnDeclarations=*/false);
  ExitOnErr(Importer.importFunctions(DestModule, ImportList));

  return true;
}

static std::unique_ptr<Module>
loadInputFile(const char *argv0, LLVMContext &Context, const std::string &File) {
  std::unique_ptr<MemoryBuffer> Buffer =
    ExitOnErr(errorOrToExpected(MemoryBuffer::getFileOrSTDIN(File)));

  std::unique_ptr<Module> M =
    identify_magic(Buffer->getBuffer()) == file_magic::archive
        ? loadArFile(argv0, std::move(Buffer), Context)
        : loadFile(argv0, std::move(Buffer), Context, true);
  if (!M.get()) {
    errs() << argv0 << ": ";
    WithColor::error() << " loading file '" << File << "'\n";
    return nullptr;
  }

  // Note that when ODR merging types cannot verify input files in here. When
  // doing that debug metadata in the src module might already be pointing to
  // the destination.
  if (DisableDITypeMap && !NoVerify && verifyModule(*M, &errs())) {
    errs() << argv0 << ": " << File << ": ";
    WithColor::error() << "input module is broken!\n";
    return nullptr;
  }

  // If a module summary index is supplied, load it so linkInModule can treat
  // local functions/variables as exported and promote if necessary.
  if (!SummaryIndex.empty()) {
    std::unique_ptr<ModuleSummaryIndex> Index =
        ExitOnErr(llvm::getModuleSummaryIndexForFile(SummaryIndex));

    // Conservatively mark all internal values as promoted, since this tool
    // does not do the ThinLink that would normally determine what values to
    // promote.
    for (auto &I : *Index) {
      for (auto &S : I.second.SummaryList) {
        if (GlobalValue::isLocalLinkage(S->linkage()))
          S->setLinkage(GlobalValue::ExternalLinkage);
      }
    }

    // Promotion
    if (renameModuleForThinLTO(*M, *Index,
                               /*ClearDSOLocalOnDeclarations=*/false)) {
      errs() << argv0 << ": " << File << ": ";
      WithColor::error() << "applying summary index file failed!\n";
      return nullptr;
    }
  }

  return M;
}

static bool linkFiles(const char *argv0, LLVMContext &Context, Linker &L,
                      const cl::list<std::string> &Files,
                      unsigned Flags) {
  // Filter out flags that don't apply to the first file we load.
  unsigned ApplicableFlags = Flags & Linker::Flags::OverrideFromSrc;
  // Similar to some flags, internalization doesn't apply to the first file.
  bool InternalizeLinkedSymbols = false;
  for (const auto &File : Files) {
    std::unique_ptr<Module> M(loadInputFile(argv0, Context, File));

    if (!M.get())
      return false;

    if (Verbose)
      errs() << "Linking in '" << File << "'\n";

    bool Err = false;
    if (InternalizeLinkedSymbols) {
      Err = L.linkInModule(
          std::move(M), ApplicableFlags, [](Module &M, const StringSet<> &GVS) {
            internalizeModule(M, [&GVS](const GlobalValue &GV) {
              return !GV.hasName() || (GVS.count(GV.getName()) == 0);
            });
          });
    } else {
      Err = L.linkInModule(std::move(M), ApplicableFlags);
    }

    if (Err)
      return false;

    // Internalization applies to linking of subsequent files.
    InternalizeLinkedSymbols = Internalize;

    // All linker flags apply to linking of subsequent files.
    ApplicableFlags = Flags;
  }

  return true;
}

struct PerThreadData {
  std::unique_ptr<Module> Composite;
  std::mutex LLock;
  std::unique_ptr<Linker> L;
};

struct Workunit {
  enum {
    // The file in InputFile is loaded into DestContext, then linked into
    // Dest->L with the given Flags. If DestContext is nullptr then a new
    // LLVMContext is created for this module and linking is performed
    // across contexts.
    LoadAndLink,

    // The module in Src->Composite is linked into Linker Dest->L with Flags.
    // Before starting, it waits on the condition variables in both SrcWorkunit
    // and DestWorkunit. DestWorkunit is only used for its condition variable.
    LinkModules,
  } Type;

  // Both LoadAndLink and LinkModules:
  PerThreadData *Dest;
  unsigned Flags = Linker::Flags::None;
  bool Internalize = false;

  // LoadAndLink only:
  LLVMContext *DestContext = nullptr;
  std::string InputFile;

  // LinkModules only:
  Workunit *SrcWorkunit = nullptr;
  Workunit *DestWorkunit = nullptr;

  // All work units. Notified upon completion of this workunit.
  bool Done = false;
  std::mutex CondLock;
  std::condition_variable Cond;
};

static const char *argv0 = nullptr;

static void executeWorkunits(std::vector<std::unique_ptr<Workunit>> *Workunits) {
  for (auto &wu_ptr : *Workunits) {
    auto &wu = *wu_ptr;
    assert(!wu.Done && "Duplicate workunit in list.");

    if (wu.DestWorkunit) {
      assert(wu.Type == Workunit::LinkModules);
      std::unique_lock<std::mutex> lock(wu.DestWorkunit->CondLock);
      if (!wu.DestWorkunit->Done)
        wu.DestWorkunit->Cond.wait(lock, [&]{ return !wu.DestWorkunit->Done; });
    }
    if (wu.SrcWorkunit) {
      assert(wu.Type == Workunit::LinkModules);
      std::unique_lock<std::mutex> lock(wu.SrcWorkunit->CondLock);
      if (!wu.SrcWorkunit->Done)
        wu.SrcWorkunit->Cond.wait(lock, [&]{ return !wu.SrcWorkunit->Done; });
    }

    auto link = [&](std::unique_ptr<Module> &&M) {
      std::unique_lock<std::mutex> lock(wu.Dest->LLock);

      // Happens when an error was encountered earlier.
      if (!wu.Dest->L)
        return;

      bool Err;
      if (wu.Internalize) {
        Err = wu.Dest->L->linkInModule(std::move(M), wu.Flags, [](Module &M, const StringSet<> &GVS) {
          internalizeModule(M, [&GVS](const GlobalValue &GV) {
            return !GV.hasName() || (GVS.count(GV.getName()) == 0);
          });
        });
      } else {
        Err = wu.Dest->L->linkInModule(std::move(M), wu.Flags);
      }
      if (Err) {
        wu.Dest->L.reset();
      }
    };

    switch (wu.Type) {
    case Workunit::LoadAndLink: {
      auto M = loadInputFile(argv0, *wu.DestContext, wu.InputFile);
      if (!M) {
        wu.Dest->L.reset();
        break;
      }
      link(std::move(M));
      break;
    }
    case Workunit::LinkModules: {
      auto &SrcModule = wu.SrcWorkunit->Dest->Composite;
      link(std::move(SrcModule));
      break;
    }
    }

    std::unique_lock<std::mutex> lock(wu.CondLock);
    wu.Done = true;
    wu.Cond.notify_all();
  }
}

static LLVMContext *newContext() {
  LLVMContext *ctx = new LLVMContext;
  ctx->setDiagnosticHandler(
    std::make_unique<LLVMLinkDiagnosticHandler>(), true);
  if (!DisableDITypeMap)
    ctx->enableDebugTypeODRUniquing();
  return ctx;
}

int main(int argc, char **argv) {
  InitLLVM X(argc, argv);
  ExitOnErr.setBanner(std::string(argv[0]) + ": ");

  cl::ParseCommandLineOptions(argc, argv, "llvm linker\n");
  argv0 = argv[0];

  unsigned Flags = Linker::Flags::None;
  if (OnlyNeeded)
    Flags |= Linker::Flags::LinkOnlyNeeded;

  ThreadPoolStrategy S = hardware_concurrency(NumThreads);
  if (NumThreads == 0) {
    // If NumThreads is not specified, create one thread for each input, up to
    // the number of hardware cores.
    S = heavyweight_hardware_concurrency(InputFilenames.size());
    S.Limit = true;
  }
  ThreadPool Pool(S);

  // Construct work units depending on the settings.

  std::vector<std::vector<std::unique_ptr<Workunit>>> WorkunitsByThread(Pool.getThreadCount());
  std::vector<PerThreadData> ThreadData(Pool.getThreadCount());

  for (unsigned thread = 0; thread != Pool.getThreadCount(); ++thread) {
    auto &data = ThreadData[thread];
    data.Composite = std::make_unique<Module>("llvm-link", *newContext());
    data.L = std::make_unique<Linker>(*data.Composite);
  }

  // Files are loaded and then linked within their thread.
  unsigned thread = 0;
  bool first_link = true;
  for (auto &File : InputFilenames) {
    auto wu = std::make_unique<Workunit>();
    wu->Type = Workunit::LoadAndLink;
    wu->DestContext = ContextEachInput ? nullptr : &ThreadData[thread].Composite->getContext();
    wu->InputFile = File;
    wu->Dest = &ThreadData[thread];
    wu->Flags = first_link ? Flags & Linker::Flags::OverrideFromSrc : Flags;
    wu->Internalize = !first_link && Internalize;

    WorkunitsByThread[thread].push_back(std::move(wu));

    ++thread;
    if (thread == Pool.getThreadCount()) {
      first_link = false;
      thread = 0;
    }
  }

  // Finally, we need to fold them into one. We merge them pairwise forming a
  // tree that resembles a sporting tournament where the winner (Dest) goes on
  // to the next round. The algorithm is:
  // * Take each pair of modules and fold the the second into the first
  //   (link #1 into #0, link #3 into #2, etc).
  // * Remove #1, #3, etc. because those are no longer needed, renumbering
  //   the ones that follow it, #2 -> #1, #4 -> #2, etc.)
  // * Repeat until there is only one left.
  // As an optimization we don't renumber them, instead we skip over the
  // modules that have already been used as link sources when forming pairs.
  for (unsigned depth = 1; depth < Pool.getThreadCount(); depth <<= 1) {
    for (unsigned i = depth; i < Pool.getThreadCount(); i += depth) {
      auto wu = std::make_unique<Workunit>();
      wu->Type = Workunit::LinkModules;
      wu->Dest = &ThreadData[i - depth];
      wu->DestWorkunit = WorkunitsByThread[i - depth].back().get();
      wu->SrcWorkunit = WorkunitsByThread[i].back().get();
      wu->Flags = Flags;
      wu->Internalize = Internalize;
      WorkunitsByThread[i - depth].push_back(std::move(wu));
    }
  }

  for (std::vector<std::unique_ptr<Workunit>> &WorkForThread : WorkunitsByThread) {
    Pool.async(&executeWorkunits, &WorkForThread);
  }
  Pool.wait();

  if (!ThreadData[0].L)
    return 1;

  auto Composite = std::move(ThreadData[0].Composite);
  auto &Context = Composite->getContext();
  Linker &L = *ThreadData[0].L;

  // Next the -override ones.
  if (!linkFiles(argv[0], Context, L, OverridingInputs,
                 Flags | Linker::Flags::OverrideFromSrc))
    return 1;

  // Import any functions requested via -import
  if (!importFunctions(argv[0], *Composite))
    return 1;

  if (DumpAsm)
    errs() << "Here's the assembly:\n" << *Composite;

  std::error_code EC;
  ToolOutputFile Out(OutputFilename, EC,
                     OutputAssembly ? sys::fs::OF_TextWithCRLF
                                    : sys::fs::OF_None);
  if (EC) {
    WithColor::error() << EC.message() << '\n';
    return 1;
  }

  if (!NoVerify && verifyModule(*Composite, &errs())) {
    errs() << argv[0] << ": ";
    WithColor::error() << "linked module is broken!\n";
    return 1;
  }

  if (Verbose)
    errs() << "Writing bitcode...\n";
  if (OutputAssembly) {
    Composite->print(Out.os(), nullptr, PreserveAssemblyUseListOrder);
  } else if (Force || !CheckBitcodeOutputToConsole(Out.os()))
    WriteBitcodeToFile(*Composite, Out.os(), PreserveBitcodeUseListOrder);

  // Declare success.
  Out.keep();

  return 0;
}
