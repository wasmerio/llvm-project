; This one fails because the LLVM runtime is allowing two null pointers of
; the same type to be created!

; RUN: echo "%%T = type i32" > %t.2.ll
; RUN: llvm-link %s %t.2.ll
; RUN: llvm-link --context-each-input %s %t.2.ll

%T = type opaque

declare %T* @create()

define void @test() {
	%X = call %T* @create( )		; <%T*> [#uses=1]
	%v = icmp eq %T* %X, null		; <i1> [#uses=0]
	ret void
}

