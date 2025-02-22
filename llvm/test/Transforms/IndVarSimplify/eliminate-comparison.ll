; NOTE: Assertions have been autogenerated by utils/update_test_checks.py
; RUN: opt -indvars -S < %s | FileCheck %s

target datalayout = "e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:128:128-a0:0:64-s0:64:64-f80:128:128-n8:16:32:64"

@X = external global [0 x double]

; Indvars should be able to simplify simple comparisons involving
; induction variables.

define void @foo(i64 %n, i32* nocapture %p) nounwind {
; CHECK-LABEL: @foo(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    [[CMP9:%.*]] = icmp sgt i64 [[N:%.*]], 0
; CHECK-NEXT:    br i1 [[CMP9]], label [[PRE:%.*]], label [[RETURN:%.*]]
; CHECK:       pre:
; CHECK-NEXT:    [[T3:%.*]] = load i32, i32* [[P:%.*]], align 4
; CHECK-NEXT:    [[TOBOOL_NOT:%.*]] = icmp ne i32 [[T3]], 0
; CHECK-NEXT:    br label [[LOOP:%.*]]
; CHECK:       loop:
; CHECK-NEXT:    [[I:%.*]] = phi i64 [ 0, [[PRE]] ], [ [[INC:%.*]], [[FOR_INC:%.*]] ]
; CHECK-NEXT:    [[COND:%.*]] = and i1 [[TOBOOL_NOT]], true
; CHECK-NEXT:    br i1 [[COND]], label [[IF_THEN:%.*]], label [[FOR_INC]]
; CHECK:       if.then:
; CHECK-NEXT:    [[ARRAYIDX:%.*]] = getelementptr [0 x double], [0 x double]* @X, i64 0, i64 [[I]]
; CHECK-NEXT:    store double 3.200000e+00, double* [[ARRAYIDX]], align 8
; CHECK-NEXT:    br label [[FOR_INC]]
; CHECK:       for.inc:
; CHECK-NEXT:    [[INC]] = add nuw nsw i64 [[I]], 1
; CHECK-NEXT:    [[EXITCOND1:%.*]] = icmp eq i64 [[INC]], [[N]]
; CHECK-NEXT:    br i1 [[EXITCOND1]], label [[RETURN_LOOPEXIT:%.*]], label [[LOOP]]
; CHECK:       return.loopexit:
; CHECK-NEXT:    br label [[RETURN]]
; CHECK:       return:
; CHECK-NEXT:    ret void
;
entry:
  %cmp9 = icmp sgt i64 %n, 0
  br i1 %cmp9, label %pre, label %return

pre:
  %t3 = load i32, i32* %p
  %tobool.not = icmp ne i32 %t3, 0
  br label %loop

loop:
  %i = phi i64 [ 0, %pre ], [ %inc, %for.inc ]
  %cmp6 = icmp slt i64 %i, %n
  %cond = and i1 %tobool.not, %cmp6
  br i1 %cond, label %if.then, label %for.inc

if.then:
  %arrayidx = getelementptr [0 x double], [0 x double]* @X, i64 0, i64 %i
  store double 3.200000e+00, double* %arrayidx
  br label %for.inc

for.inc:
  %inc = add nsw i64 %i, 1
  %exitcond = icmp sge i64 %inc, %n
  br i1 %exitcond, label %return, label %loop

return:
  ret void
}

; Don't eliminate an icmp that's contributing to the loop exit test though.

define i32 @_ZNK4llvm5APInt3ultERKS0_(i32 %tmp2.i1, i64** %tmp65, i64** %tmp73, i64** %tmp82, i64** %tmp90) {
; CHECK-LABEL: @_ZNK4llvm5APInt3ultERKS0_(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    br label [[BB18:%.*]]
; CHECK:       bb13:
; CHECK-NEXT:    [[TMP66:%.*]] = load i64*, i64** [[TMP65:%.*]], align 4
; CHECK-NEXT:    [[TMP68:%.*]] = getelementptr inbounds i64, i64* [[TMP66]], i32 [[I:%.*]]
; CHECK-NEXT:    [[TMP69:%.*]] = load i64, i64* [[TMP68]], align 4
; CHECK-NEXT:    [[TMP74:%.*]] = load i64*, i64** [[TMP73:%.*]], align 4
; CHECK-NEXT:    [[TMP76:%.*]] = getelementptr inbounds i64, i64* [[TMP74]], i32 [[I]]
; CHECK-NEXT:    [[TMP77:%.*]] = load i64, i64* [[TMP76]], align 4
; CHECK-NEXT:    [[TMP78:%.*]] = icmp ugt i64 [[TMP69]], [[TMP77]]
; CHECK-NEXT:    br i1 [[TMP78]], label [[BB20_LOOPEXIT:%.*]], label [[BB15:%.*]]
; CHECK:       bb15:
; CHECK-NEXT:    [[TMP83:%.*]] = load i64*, i64** [[TMP82:%.*]], align 4
; CHECK-NEXT:    [[TMP85:%.*]] = getelementptr inbounds i64, i64* [[TMP83]], i32 [[I]]
; CHECK-NEXT:    [[TMP86:%.*]] = load i64, i64* [[TMP85]], align 4
; CHECK-NEXT:    [[TMP91:%.*]] = load i64*, i64** [[TMP90:%.*]], align 4
; CHECK-NEXT:    [[TMP93:%.*]] = getelementptr inbounds i64, i64* [[TMP91]], i32 [[I]]
; CHECK-NEXT:    [[TMP94:%.*]] = load i64, i64* [[TMP93]], align 4
; CHECK-NEXT:    [[TMP95:%.*]] = icmp ult i64 [[TMP86]], [[TMP94]]
; CHECK-NEXT:    br i1 [[TMP95]], label [[BB20_LOOPEXIT]], label [[BB17:%.*]]
; CHECK:       bb17:
; CHECK-NEXT:    [[TMP97:%.*]] = add nsw i32 [[I]], -1
; CHECK-NEXT:    br label [[BB18]]
; CHECK:       bb18:
; CHECK-NEXT:    [[I]] = phi i32 [ [[TMP2_I1:%.*]], [[ENTRY:%.*]] ], [ [[TMP97]], [[BB17]] ]
; CHECK-NEXT:    [[TMP99:%.*]] = icmp sgt i32 [[I]], -1
; CHECK-NEXT:    br i1 [[TMP99]], label [[BB13:%.*]], label [[BB20_LOOPEXIT]]
; CHECK:       bb20.loopexit:
; CHECK-NEXT:    [[TMP_0_PH:%.*]] = phi i32 [ 0, [[BB18]] ], [ 1, [[BB15]] ], [ 0, [[BB13]] ]
; CHECK-NEXT:    ret i32 [[TMP_0_PH]]
;
entry:
  br label %bb18

bb13:
  %tmp66 = load i64*, i64** %tmp65, align 4
  %tmp68 = getelementptr inbounds i64, i64* %tmp66, i32 %i
  %tmp69 = load i64, i64* %tmp68, align 4
  %tmp74 = load i64*, i64** %tmp73, align 4
  %tmp76 = getelementptr inbounds i64, i64* %tmp74, i32 %i
  %tmp77 = load i64, i64* %tmp76, align 4
  %tmp78 = icmp ugt i64 %tmp69, %tmp77
  br i1 %tmp78, label %bb20.loopexit, label %bb15

bb15:
  %tmp83 = load i64*, i64** %tmp82, align 4
  %tmp85 = getelementptr inbounds i64, i64* %tmp83, i32 %i
  %tmp86 = load i64, i64* %tmp85, align 4
  %tmp91 = load i64*, i64** %tmp90, align 4
  %tmp93 = getelementptr inbounds i64, i64* %tmp91, i32 %i
  %tmp94 = load i64, i64* %tmp93, align 4
  %tmp95 = icmp ult i64 %tmp86, %tmp94
  br i1 %tmp95, label %bb20.loopexit, label %bb17

bb17:
  %tmp97 = add nsw i32 %i, -1
  br label %bb18

bb18:
  %i = phi i32 [ %tmp2.i1, %entry ], [ %tmp97, %bb17 ]
  %tmp99 = icmp sgt i32 %i, -1
  br i1 %tmp99, label %bb13, label %bb20.loopexit

bb20.loopexit:
  %tmp.0.ph = phi i32 [ 0, %bb18 ], [ 1, %bb15 ], [ 0, %bb13 ]
  ret i32 %tmp.0.ph
}

; Indvars should eliminate the icmp here.


define void @func_10() nounwind {
; CHECK-LABEL: @func_10(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    br label [[LOOP:%.*]]
; CHECK:       loop:
; CHECK-NEXT:    [[INDVARS_IV:%.*]] = phi i64 [ [[INDVARS_IV_NEXT:%.*]], [[LOOP]] ], [ 0, [[ENTRY:%.*]] ]
; CHECK-NEXT:    store i64 [[INDVARS_IV]], i64* null, align 8
; CHECK-NEXT:    [[INDVARS_IV_NEXT]] = add nuw nsw i64 [[INDVARS_IV]], 1
; CHECK-NEXT:    br i1 false, label [[LOOP]], label [[RETURN:%.*]]
; CHECK:       return:
; CHECK-NEXT:    ret void
;
entry:
  br label %loop

loop:
  %i = phi i32 [ %i.next, %loop ], [ 0, %entry ]
  %t0 = icmp slt i32 %i, 0
  %t1 = zext i1 %t0 to i32
  %t2 = add i32 %t1, %i
  %u3 = zext i32 %t2 to i64
  store i64 %u3, i64* null
  %i.next = add i32 %i, 1
  br i1 undef, label %loop, label %return

return:
  ret void
}

; PR14432
; Indvars should not turn the second loop into an infinite one.


define i32 @func_11() nounwind uwtable {
; CHECK-LABEL: @func_11(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    br label [[FORCOND:%.*]]
; CHECK:       forcond:
; CHECK-NEXT:    br i1 false, label [[NOASSERT:%.*]], label [[FORCOND38_PREHEADER:%.*]]
; CHECK:       forcond38.preheader:
; CHECK-NEXT:    br label [[FORCOND38:%.*]]
; CHECK:       noassert:
; CHECK-NEXT:    br i1 true, label [[FORCOND]], label [[ASSERT33:%.*]]
; CHECK:       assert33:
; CHECK-NEXT:    tail call void @llvm.trap()
; CHECK-NEXT:    unreachable
; CHECK:       forcond38:
; CHECK-NEXT:    br i1 false, label [[NOASSERT68:%.*]], label [[UNROLLEDEND:%.*]]
; CHECK:       noassert68:
; CHECK-NEXT:    br i1 true, label [[FORCOND38]], label [[ASSERT77:%.*]]
; CHECK:       assert77:
; CHECK-NEXT:    tail call void @llvm.trap()
; CHECK-NEXT:    unreachable
; CHECK:       unrolledend:
; CHECK-NEXT:    ret i32 0
;
entry:
  br label %forcond

forcond:                                          ; preds = %noassert, %entry
  %__key6.0 = phi i32 [ 2, %entry ], [ %tmp37, %noassert ]
  %tmp5 = icmp slt i32 %__key6.0, 10
  br i1 %tmp5, label %noassert, label %forcond38.preheader

forcond38.preheader:                              ; preds = %forcond
  br label %forcond38

noassert:                                         ; preds = %forbody
  %tmp13 = sdiv i32 -32768, %__key6.0
  %tmp2936 = shl i32 %tmp13, 24
  %sext23 = shl i32 %tmp13, 24
  %tmp32 = icmp eq i32 %tmp2936, %sext23
  %tmp37 = add i32 %__key6.0, 1
  br i1 %tmp32, label %forcond, label %assert33

assert33:                                         ; preds = %noassert
  tail call void @llvm.trap()
  unreachable

forcond38:                                        ; preds = %noassert68, %forcond38.preheader
  %__key8.0 = phi i32 [ %tmp81, %noassert68 ], [ 2, %forcond38.preheader ]
  %tmp46 = icmp slt i32 %__key8.0, 10
  br i1 %tmp46, label %noassert68, label %unrolledend

noassert68:                                       ; preds = %forbody39
  %tmp57 = sdiv i32 -32768, %__key8.0
  %sext34 = shl i32 %tmp57, 16
  %sext21 = shl i32 %tmp57, 16
  %tmp76 = icmp eq i32 %sext34, %sext21
  %tmp81 = add i32 %__key8.0, 1
  br i1 %tmp76, label %forcond38, label %assert77

assert77:                                         ; preds = %noassert68
  tail call void @llvm.trap()
  unreachable

unrolledend:                                      ; preds = %forcond38
  ret i32 0
}

define i32 @func_11_flipped() nounwind uwtable {
; CHECK-LABEL: @func_11_flipped(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    br label [[FORCOND:%.*]]
; CHECK:       forcond:
; CHECK-NEXT:    br i1 true, label [[FORCOND38_PREHEADER:%.*]], label [[NOASSERT:%.*]]
; CHECK:       forcond38.preheader:
; CHECK-NEXT:    br label [[FORCOND38:%.*]]
; CHECK:       noassert:
; CHECK-NEXT:    br i1 true, label [[FORCOND]], label [[ASSERT33:%.*]]
; CHECK:       assert33:
; CHECK-NEXT:    tail call void @llvm.trap()
; CHECK-NEXT:    unreachable
; CHECK:       forcond38:
; CHECK-NEXT:    br i1 false, label [[NOASSERT68:%.*]], label [[UNROLLEDEND:%.*]]
; CHECK:       noassert68:
; CHECK-NEXT:    br i1 true, label [[FORCOND38]], label [[ASSERT77:%.*]]
; CHECK:       assert77:
; CHECK-NEXT:    tail call void @llvm.trap()
; CHECK-NEXT:    unreachable
; CHECK:       unrolledend:
; CHECK-NEXT:    ret i32 0
;
entry:
  br label %forcond

forcond:                                          ; preds = %noassert, %entry
  %__key6.0 = phi i32 [ 2, %entry ], [ %tmp37, %noassert ]
  %tmp5 = icmp sge i32 %__key6.0, 10
  br i1 %tmp5, label %forcond38.preheader, label %noassert

forcond38.preheader:                              ; preds = %forcond
  br label %forcond38

noassert:                                         ; preds = %forbody
  %tmp13 = sdiv i32 -32768, %__key6.0
  %tmp2936 = shl i32 %tmp13, 24
  %sext23 = shl i32 %tmp13, 24
  %tmp32 = icmp eq i32 %tmp2936, %sext23
  %tmp37 = add i32 %__key6.0, 1
  br i1 %tmp32, label %forcond, label %assert33

assert33:                                         ; preds = %noassert
  tail call void @llvm.trap()
  unreachable

forcond38:                                        ; preds = %noassert68, %forcond38.preheader
  %__key8.0 = phi i32 [ %tmp81, %noassert68 ], [ 2, %forcond38.preheader ]
  %tmp46 = icmp slt i32 %__key8.0, 10
  br i1 %tmp46, label %noassert68, label %unrolledend

noassert68:                                       ; preds = %forbody39
  %tmp57 = sdiv i32 -32768, %__key8.0
  %sext34 = shl i32 %tmp57, 16
  %sext21 = shl i32 %tmp57, 16
  %tmp76 = icmp eq i32 %sext34, %sext21
  %tmp81 = add i32 %__key8.0, 1
  br i1 %tmp76, label %forcond38, label %assert77

assert77:                                         ; preds = %noassert68
  tail call void @llvm.trap()
  unreachable

unrolledend:                                      ; preds = %forcond38
  ret i32 0
}

declare void @llvm.trap() noreturn nounwind

; In this case the second loop only has a single iteration, fold the header away
define i32 @func_12() nounwind uwtable {
; CHECK-LABEL: @func_12(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    br label [[FORCOND:%.*]]
; CHECK:       forcond:
; CHECK-NEXT:    br i1 false, label [[NOASSERT:%.*]], label [[FORCOND38_PREHEADER:%.*]]
; CHECK:       forcond38.preheader:
; CHECK-NEXT:    br label [[FORCOND38:%.*]]
; CHECK:       noassert:
; CHECK-NEXT:    br i1 true, label [[FORCOND]], label [[ASSERT33:%.*]]
; CHECK:       assert33:
; CHECK-NEXT:    tail call void @llvm.trap()
; CHECK-NEXT:    unreachable
; CHECK:       forcond38:
; CHECK-NEXT:    br i1 true, label [[NOASSERT68:%.*]], label [[UNROLLEDEND:%.*]]
; CHECK:       noassert68:
; CHECK-NEXT:    br i1 false, label [[FORCOND38]], label [[ASSERT77:%.*]]
; CHECK:       assert77:
; CHECK-NEXT:    tail call void @llvm.trap()
; CHECK-NEXT:    unreachable
; CHECK:       unrolledend:
; CHECK-NEXT:    ret i32 0
;
entry:
  br label %forcond

forcond:                                          ; preds = %noassert, %entry
  %__key6.0 = phi i32 [ 2, %entry ], [ %tmp37, %noassert ]
  %tmp5 = icmp slt i32 %__key6.0, 10
  br i1 %tmp5, label %noassert, label %forcond38.preheader

forcond38.preheader:                              ; preds = %forcond
  br label %forcond38

noassert:                                         ; preds = %forbody
  %tmp13 = sdiv i32 -32768, %__key6.0
  %tmp2936 = shl i32 %tmp13, 24
  %sext23 = shl i32 %tmp13, 24
  %tmp32 = icmp eq i32 %tmp2936, %sext23
  %tmp37 = add i32 %__key6.0, 1
  br i1 %tmp32, label %forcond, label %assert33

assert33:                                         ; preds = %noassert
  tail call void @llvm.trap()
  unreachable

forcond38:                                        ; preds = %noassert68, %forcond38.preheader
  %__key8.0 = phi i32 [ %tmp81, %noassert68 ], [ 2, %forcond38.preheader ]
  %tmp46 = icmp slt i32 %__key8.0, 10
  br i1 %tmp46, label %noassert68, label %unrolledend

noassert68:                                       ; preds = %forbody39
  %tmp57 = sdiv i32 -32768, %__key8.0
  %sext34 = shl i32 %tmp57, 16
  %sext21 = shl i32 %tmp57, 16
  %tmp76 = icmp ne i32 %sext34, %sext21
  %tmp81 = add i32 %__key8.0, 1
  br i1 %tmp76, label %forcond38, label %assert77

assert77:                                         ; preds = %noassert68
  tail call void @llvm.trap()
  unreachable

unrolledend:                                      ; preds = %forcond38
  ret i32 0
}

declare void @side_effect()

define void @func_13(i32* %len.ptr) {
; CHECK-LABEL: @func_13(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    [[LEN:%.*]] = load i32, i32* [[LEN_PTR:%.*]], align 4, !range [[RNG0:![0-9]+]]
; CHECK-NEXT:    [[LEN_IS_ZERO:%.*]] = icmp eq i32 [[LEN]], 0
; CHECK-NEXT:    br i1 [[LEN_IS_ZERO]], label [[LEAVE:%.*]], label [[LOOP_PREHEADER:%.*]]
; CHECK:       loop.preheader:
; CHECK-NEXT:    br label [[LOOP:%.*]]
; CHECK:       loop:
; CHECK-NEXT:    [[IV:%.*]] = phi i32 [ [[IV_INC:%.*]], [[BE:%.*]] ], [ 0, [[LOOP_PREHEADER]] ]
; CHECK-NEXT:    call void @side_effect()
; CHECK-NEXT:    [[IV_INC]] = add nuw nsw i32 [[IV]], 1
; CHECK-NEXT:    br i1 true, label [[BE]], label [[LEAVE_LOOPEXIT:%.*]]
; CHECK:       be:
; CHECK-NEXT:    call void @side_effect()
; CHECK-NEXT:    [[EXITCOND:%.*]] = icmp ne i32 [[IV_INC]], [[LEN]]
; CHECK-NEXT:    br i1 [[EXITCOND]], label [[LOOP]], label [[LEAVE_LOOPEXIT]]
; CHECK:       leave.loopexit:
; CHECK-NEXT:    br label [[LEAVE]]
; CHECK:       leave:
; CHECK-NEXT:    ret void
;
entry:
  %len = load i32, i32* %len.ptr, !range !0
  %len.sub.1 = add i32 %len, -1
  %len.is.zero = icmp eq i32 %len, 0
  br i1 %len.is.zero, label %leave, label %loop

loop:
  %iv = phi i32 [ 0, %entry ], [ %iv.inc, %be ]
  call void @side_effect()
  %iv.inc = add i32 %iv, 1
  %iv.cmp = icmp ult i32 %iv, %len
  br i1 %iv.cmp, label %be, label %leave

be:
  call void @side_effect()
  %be.cond = icmp ult i32 %iv, %len.sub.1
  br i1 %be.cond, label %loop, label %leave

leave:
  ret void
}

define void @func_14(i32* %len.ptr) {
; CHECK-LABEL: @func_14(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    [[LEN:%.*]] = load i32, i32* [[LEN_PTR:%.*]], align 4, !range [[RNG0]]
; CHECK-NEXT:    [[LEN_IS_ZERO:%.*]] = icmp eq i32 [[LEN]], 0
; CHECK-NEXT:    [[LEN_IS_INT_MIN:%.*]] = icmp eq i32 [[LEN]], -2147483648
; CHECK-NEXT:    [[NO_ENTRY:%.*]] = or i1 [[LEN_IS_ZERO]], [[LEN_IS_INT_MIN]]
; CHECK-NEXT:    br i1 [[NO_ENTRY]], label [[LEAVE:%.*]], label [[LOOP_PREHEADER:%.*]]
; CHECK:       loop.preheader:
; CHECK-NEXT:    br label [[LOOP:%.*]]
; CHECK:       loop:
; CHECK-NEXT:    [[IV:%.*]] = phi i32 [ [[IV_INC:%.*]], [[BE:%.*]] ], [ 0, [[LOOP_PREHEADER]] ]
; CHECK-NEXT:    call void @side_effect()
; CHECK-NEXT:    [[IV_INC]] = add nuw nsw i32 [[IV]], 1
; CHECK-NEXT:    br i1 true, label [[BE]], label [[LEAVE_LOOPEXIT:%.*]]
; CHECK:       be:
; CHECK-NEXT:    call void @side_effect()
; CHECK-NEXT:    [[EXITCOND:%.*]] = icmp ne i32 [[IV_INC]], [[LEN]]
; CHECK-NEXT:    br i1 [[EXITCOND]], label [[LOOP]], label [[LEAVE_LOOPEXIT]]
; CHECK:       leave.loopexit:
; CHECK-NEXT:    br label [[LEAVE]]
; CHECK:       leave:
; CHECK-NEXT:    ret void
;
entry:
  %len = load i32, i32* %len.ptr, !range !0
  %len.sub.1 = add i32 %len, -1
  %len.is.zero = icmp eq i32 %len, 0
  %len.is.int_min = icmp eq i32 %len, 2147483648
  %no.entry = or i1 %len.is.zero, %len.is.int_min
  br i1 %no.entry, label %leave, label %loop

loop:
  %iv = phi i32 [ 0, %entry ], [ %iv.inc, %be ]
  call void @side_effect()
  %iv.inc = add i32 %iv, 1
  %iv.cmp = icmp slt i32 %iv, %len
  br i1 %iv.cmp, label %be, label %leave

be:
  call void @side_effect()
  %be.cond = icmp slt i32 %iv, %len.sub.1
  br i1 %be.cond, label %loop, label %leave

leave:
  ret void
}

define void @func_15(i32* %len.ptr) {
; CHECK-LABEL: @func_15(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    [[LEN:%.*]] = load i32, i32* [[LEN_PTR:%.*]], align 4, !range [[RNG0]]
; CHECK-NEXT:    [[LEN_ADD_1:%.*]] = add i32 [[LEN]], 1
; CHECK-NEXT:    [[LEN_ADD_1_IS_ZERO:%.*]] = icmp eq i32 [[LEN_ADD_1]], 0
; CHECK-NEXT:    br i1 [[LEN_ADD_1_IS_ZERO]], label [[LEAVE:%.*]], label [[LOOP_PREHEADER:%.*]]
; CHECK:       loop.preheader:
; CHECK-NEXT:    br label [[LOOP:%.*]]
; CHECK:       loop:
; CHECK-NEXT:    [[IV:%.*]] = phi i32 [ [[IV_INC:%.*]], [[BE:%.*]] ], [ 0, [[LOOP_PREHEADER]] ]
; CHECK-NEXT:    call void @side_effect()
; CHECK-NEXT:    [[IV_INC]] = add nuw nsw i32 [[IV]], 1
; CHECK-NEXT:    br i1 true, label [[BE]], label [[LEAVE_LOOPEXIT:%.*]]
; CHECK:       be:
; CHECK-NEXT:    call void @side_effect()
; CHECK-NEXT:    [[EXITCOND:%.*]] = icmp ne i32 [[IV_INC]], [[LEN_ADD_1]]
; CHECK-NEXT:    br i1 [[EXITCOND]], label [[LOOP]], label [[LEAVE_LOOPEXIT]]
; CHECK:       leave.loopexit:
; CHECK-NEXT:    br label [[LEAVE]]
; CHECK:       leave:
; CHECK-NEXT:    ret void
;
entry:
  %len = load i32, i32* %len.ptr, !range !0
  %len.add.1 = add i32 %len, 1
  %len.add.1.is.zero = icmp eq i32 %len.add.1, 0
  br i1 %len.add.1.is.zero, label %leave, label %loop

loop:
  %iv = phi i32 [ 0, %entry ], [ %iv.inc, %be ]
  call void @side_effect()
  %iv.inc = add i32 %iv, 1
  %iv.cmp = icmp ult i32 %iv, %len.add.1
  br i1 %iv.cmp, label %be, label %leave

be:
  call void @side_effect()
  %be.cond = icmp ult i32 %iv, %len
  br i1 %be.cond, label %loop, label %leave

leave:
  ret void
}

define void @func_16(i32* %len.ptr) {
; CHECK-LABEL: @func_16(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    [[LEN:%.*]] = load i32, i32* [[LEN_PTR:%.*]], align 4, !range [[RNG0]]
; CHECK-NEXT:    [[LEN_ADD_5:%.*]] = add i32 [[LEN]], 5
; CHECK-NEXT:    [[ENTRY_COND_0:%.*]] = icmp slt i32 [[LEN]], 2147483643
; CHECK-NEXT:    [[ENTRY_COND_1:%.*]] = icmp slt i32 4, [[LEN_ADD_5]]
; CHECK-NEXT:    [[ENTRY_COND:%.*]] = and i1 [[ENTRY_COND_0]], [[ENTRY_COND_1]]
; CHECK-NEXT:    br i1 [[ENTRY_COND]], label [[LOOP_PREHEADER:%.*]], label [[LEAVE:%.*]]
; CHECK:       loop.preheader:
; CHECK-NEXT:    [[TMP0:%.*]] = add nuw nsw i32 [[LEN]], 1
; CHECK-NEXT:    br label [[LOOP:%.*]]
; CHECK:       loop:
; CHECK-NEXT:    [[IV:%.*]] = phi i32 [ [[IV_INC:%.*]], [[BE:%.*]] ], [ 0, [[LOOP_PREHEADER]] ]
; CHECK-NEXT:    call void @side_effect()
; CHECK-NEXT:    [[IV_INC]] = add nuw nsw i32 [[IV]], 1
; CHECK-NEXT:    br i1 true, label [[BE]], label [[LEAVE_LOOPEXIT:%.*]]
; CHECK:       be:
; CHECK-NEXT:    call void @side_effect()
; CHECK-NEXT:    [[EXITCOND:%.*]] = icmp ne i32 [[IV_INC]], [[TMP0]]
; CHECK-NEXT:    br i1 [[EXITCOND]], label [[LOOP]], label [[LEAVE_LOOPEXIT]]
; CHECK:       leave.loopexit:
; CHECK-NEXT:    br label [[LEAVE]]
; CHECK:       leave:
; CHECK-NEXT:    ret void
;
entry:
  %len = load i32, i32* %len.ptr, !range !0
  %len.add.5 = add i32 %len, 5
  %entry.cond.0 = icmp slt i32 %len, 2147483643
  %entry.cond.1 = icmp slt i32 4, %len.add.5
  %entry.cond = and i1 %entry.cond.0, %entry.cond.1
  br i1 %entry.cond, label %loop, label %leave

loop:
  %iv = phi i32 [ 0, %entry ], [ %iv.inc, %be ]
  call void @side_effect()
  %iv.inc = add i32 %iv, 1
  %iv.add.4 = add i32 %iv, 4
  %iv.cmp = icmp slt i32 %iv.add.4, %len.add.5
  br i1 %iv.cmp, label %be, label %leave

be:
  call void @side_effect()
  %be.cond = icmp slt i32 %iv, %len
  br i1 %be.cond, label %loop, label %leave

leave:
  ret void
}

define void @func_17(i32* %len.ptr) {
; CHECK-LABEL: @func_17(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    [[LEN:%.*]] = load i32, i32* [[LEN_PTR:%.*]], align 4
; CHECK-NEXT:    [[LEN_ADD_5:%.*]] = add i32 [[LEN]], -5
; CHECK-NEXT:    [[ENTRY_COND_0:%.*]] = icmp slt i32 [[LEN]], -2147483643
; CHECK-NEXT:    [[ENTRY_COND_1:%.*]] = icmp slt i32 -6, [[LEN_ADD_5]]
; CHECK-NEXT:    [[ENTRY_COND:%.*]] = and i1 [[ENTRY_COND_0]], [[ENTRY_COND_1]]
; CHECK-NEXT:    br i1 [[ENTRY_COND]], label [[LOOP_PREHEADER:%.*]], label [[LEAVE:%.*]]
; CHECK:       loop.preheader:
; CHECK-NEXT:    [[SMAX:%.*]] = call i32 @llvm.smax.i32(i32 [[LEN]], i32 0)
; CHECK-NEXT:    [[TMP0:%.*]] = add nsw i32 [[SMAX]], -5
; CHECK-NEXT:    br label [[LOOP:%.*]]
; CHECK:       loop:
; CHECK-NEXT:    [[IV:%.*]] = phi i32 [ [[IV_INC:%.*]], [[BE:%.*]] ], [ -6, [[LOOP_PREHEADER]] ]
; CHECK-NEXT:    call void @side_effect()
; CHECK-NEXT:    [[IV_INC]] = add nsw i32 [[IV]], 1
; CHECK-NEXT:    br i1 true, label [[BE]], label [[LEAVE_LOOPEXIT:%.*]]
; CHECK:       be:
; CHECK-NEXT:    call void @side_effect()
; CHECK-NEXT:    [[EXITCOND:%.*]] = icmp ne i32 [[IV_INC]], [[TMP0]]
; CHECK-NEXT:    br i1 [[EXITCOND]], label [[LOOP]], label [[LEAVE_LOOPEXIT]]
; CHECK:       leave.loopexit:
; CHECK-NEXT:    br label [[LEAVE]]
; CHECK:       leave:
; CHECK-NEXT:    ret void
;
entry:
  %len = load i32, i32* %len.ptr
  %len.add.5 = add i32 %len, -5
  %entry.cond.0 = icmp slt i32 %len, 2147483653 ;; 2147483653 == INT_MIN - (-5)
  %entry.cond.1 = icmp slt i32 -6, %len.add.5
  %entry.cond = and i1 %entry.cond.0, %entry.cond.1
  br i1 %entry.cond, label %loop, label %leave

loop:
  %iv.2 = phi i32 [ 0, %entry ], [ %iv.2.inc, %be ]
  %iv = phi i32 [ -6, %entry ], [ %iv.inc, %be ]
  call void @side_effect()
  %iv.inc = add i32 %iv, 1
  %iv.2.inc = add i32 %iv.2, 1
  %iv.cmp = icmp slt i32 %iv, %len.add.5

; Deduces {-5,+,1} s< (-5 + %len) from {0,+,1} < %len
; since %len s< INT_MIN - (-5) from the entry condition
  br i1 %iv.cmp, label %be, label %leave

be:
  call void @side_effect()
  %be.cond = icmp slt i32 %iv.2, %len
  br i1 %be.cond, label %loop, label %leave

leave:
  ret void
}

define i1 @func_18(i16* %tmp20, i32* %len.addr) {
; CHECK-LABEL: @func_18(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    [[LEN:%.*]] = load i32, i32* [[LEN_ADDR:%.*]], align 4, !range [[RNG0]]
; CHECK-NEXT:    [[TMP18:%.*]] = icmp eq i32 [[LEN]], 0
; CHECK-NEXT:    br i1 [[TMP18]], label [[BB2:%.*]], label [[BB0_PREHEADER:%.*]]
; CHECK:       bb0.preheader:
; CHECK-NEXT:    br label [[BB0:%.*]]
; CHECK:       bb0:
; CHECK-NEXT:    [[VAR_0_IN:%.*]] = phi i32 [ [[VAR_0:%.*]], [[BB1:%.*]] ], [ [[LEN]], [[BB0_PREHEADER]] ]
; CHECK-NEXT:    [[VAR_1:%.*]] = phi i32 [ [[TMP30:%.*]], [[BB1]] ], [ 0, [[BB0_PREHEADER]] ]
; CHECK-NEXT:    [[VAR_0]] = add nsw i32 [[VAR_0_IN]], -1
; CHECK-NEXT:    br i1 true, label [[STAY:%.*]], label [[BB2_LOOPEXIT:%.*]]
; CHECK:       stay:
; CHECK-NEXT:    [[TMP25:%.*]] = getelementptr inbounds i16, i16* [[TMP20:%.*]], i32 [[VAR_1]]
; CHECK-NEXT:    [[TMP26:%.*]] = load i16, i16* [[TMP25]], align 2
; CHECK-NEXT:    [[TMP29:%.*]] = icmp eq i16 [[TMP26]], 0
; CHECK-NEXT:    br i1 [[TMP29]], label [[BB1]], label [[BB2_LOOPEXIT]]
; CHECK:       bb1:
; CHECK-NEXT:    [[TMP30]] = add nuw i32 [[VAR_1]], 1
; CHECK-NEXT:    [[TMP31:%.*]] = icmp eq i32 [[VAR_0]], 0
; CHECK-NEXT:    br i1 [[TMP31]], label [[BB3:%.*]], label [[BB0]]
; CHECK:       bb2.loopexit:
; CHECK-NEXT:    br label [[BB2]]
; CHECK:       bb2:
; CHECK-NEXT:    ret i1 false
; CHECK:       bb3:
; CHECK-NEXT:    ret i1 true
;
entry:
  %len = load i32, i32* %len.addr, !range !0
  %tmp18 = icmp eq i32 %len, 0
  br i1 %tmp18, label %bb2, label %bb0.preheader

bb0.preheader:
  br label %bb0

bb0:
  %var_0.in = phi i32 [ %var_0, %bb1 ], [ %len, %bb0.preheader ]
  %var_1 = phi i32 [ %tmp30, %bb1 ], [ 0, %bb0.preheader ]
  %var_0 = add nsw i32 %var_0.in, -1
  %tmp23 = icmp ult i32 %var_1, %len
  br i1 %tmp23, label %stay, label %bb2

stay:
  %tmp25 = getelementptr inbounds i16, i16* %tmp20, i32 %var_1
  %tmp26 = load i16, i16* %tmp25
  %tmp29 = icmp eq i16 %tmp26, 0
  br i1 %tmp29, label %bb1, label %bb2

bb1:
  %tmp30 = add i32 %var_1, 1
  %tmp31 = icmp eq i32 %var_0, 0
  br i1 %tmp31, label %bb3, label %bb0

bb2:
  ret i1 false

bb3:
  ret i1 true
}

define void @func_19(i32* %length.ptr) {
; CHECK-LABEL: @func_19(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    [[LENGTH:%.*]] = load i32, i32* [[LENGTH_PTR:%.*]], align 4, !range [[RNG0]]
; CHECK-NEXT:    [[LENGTH_IS_NONZERO:%.*]] = icmp ne i32 [[LENGTH]], 0
; CHECK-NEXT:    br i1 [[LENGTH_IS_NONZERO]], label [[LOOP_PREHEADER:%.*]], label [[LEAVE:%.*]]
; CHECK:       loop.preheader:
; CHECK-NEXT:    br label [[LOOP:%.*]]
; CHECK:       loop:
; CHECK-NEXT:    [[IV:%.*]] = phi i32 [ [[IV_INC:%.*]], [[BE:%.*]] ], [ 0, [[LOOP_PREHEADER]] ]
; CHECK-NEXT:    [[IV_INC]] = add nuw nsw i32 [[IV]], 1
; CHECK-NEXT:    br i1 true, label [[BE]], label [[LEAVE_LOOPEXIT:%.*]]
; CHECK:       be:
; CHECK-NEXT:    call void @side_effect()
; CHECK-NEXT:    [[EXITCOND:%.*]] = icmp ne i32 [[IV_INC]], [[LENGTH]]
; CHECK-NEXT:    br i1 [[EXITCOND]], label [[LOOP]], label [[LEAVE_LOOPEXIT]]
; CHECK:       leave.loopexit:
; CHECK-NEXT:    br label [[LEAVE]]
; CHECK:       leave:
; CHECK-NEXT:    ret void
;
entry:
  %length = load i32, i32* %length.ptr, !range !0
  %length.is.nonzero = icmp ne i32 %length, 0
  br i1 %length.is.nonzero, label %loop, label %leave

loop:
  %iv = phi i32 [ 0, %entry ], [ %iv.inc, %be ]
  %iv.inc = add i32 %iv, 1
  %range.check = icmp ult i32 %iv, %length
  br i1 %range.check, label %be, label %leave

be:
  call void @side_effect()
  %be.cond = icmp slt i32 %iv.inc, %length
  br i1 %be.cond, label %loop, label %leave

leave:
  ret void
}

; Like @func_19, but %length is no longer provably positive, so
; %range.check cannot be proved to be always true.
define void @func_20(i32* %length.ptr) {
; CHECK-LABEL: @func_20(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    [[LENGTH:%.*]] = load i32, i32* [[LENGTH_PTR:%.*]], align 4
; CHECK-NEXT:    [[LENGTH_IS_NONZERO:%.*]] = icmp ne i32 [[LENGTH]], 0
; CHECK-NEXT:    br i1 [[LENGTH_IS_NONZERO]], label [[LOOP_PREHEADER:%.*]], label [[LEAVE:%.*]]
; CHECK:       loop.preheader:
; CHECK-NEXT:    [[SMAX:%.*]] = call i32 @llvm.smax.i32(i32 [[LENGTH]], i32 1)
; CHECK-NEXT:    br label [[LOOP:%.*]]
; CHECK:       loop:
; CHECK-NEXT:    [[IV:%.*]] = phi i32 [ [[IV_INC:%.*]], [[BE:%.*]] ], [ 0, [[LOOP_PREHEADER]] ]
; CHECK-NEXT:    [[IV_INC]] = add nuw nsw i32 [[IV]], 1
; CHECK-NEXT:    [[EXITCOND:%.*]] = icmp ne i32 [[IV]], [[LENGTH]]
; CHECK-NEXT:    br i1 [[EXITCOND]], label [[BE]], label [[LEAVE_LOOPEXIT:%.*]]
; CHECK:       be:
; CHECK-NEXT:    call void @side_effect()
; CHECK-NEXT:    [[EXITCOND1:%.*]] = icmp ne i32 [[IV_INC]], [[SMAX]]
; CHECK-NEXT:    br i1 [[EXITCOND1]], label [[LOOP]], label [[LEAVE_LOOPEXIT]]
; CHECK:       leave.loopexit:
; CHECK-NEXT:    br label [[LEAVE]]
; CHECK:       leave:
; CHECK-NEXT:    ret void
;
entry:
  %length = load i32, i32* %length.ptr
  %length.is.nonzero = icmp ne i32 %length, 0
  br i1 %length.is.nonzero, label %loop, label %leave

loop:
  %iv = phi i32 [ 0, %entry ], [ %iv.inc, %be ]
  %iv.inc = add i32 %iv, 1
  %range.check = icmp ult i32 %iv, %length
  br i1 %range.check, label %be, label %leave

be:
  call void @side_effect()
  %be.cond = icmp slt i32 %iv.inc, %length
  br i1 %be.cond, label %loop, label %leave

leave:
  ret void
}

; This checks that the backedge condition, (I + 1) < Length - 1 implies
; (I + 1) < Length
define void @func_21(i32* %length.ptr) {
; CHECK-LABEL: @func_21(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    [[LENGTH:%.*]] = load i32, i32* [[LENGTH_PTR:%.*]], align 4, !range [[RNG0]]
; CHECK-NEXT:    [[LIM:%.*]] = sub i32 [[LENGTH]], 1
; CHECK-NEXT:    [[ENTRY_COND:%.*]] = icmp sgt i32 [[LENGTH]], 1
; CHECK-NEXT:    br i1 [[ENTRY_COND]], label [[LOOP_PREHEADER:%.*]], label [[LEAVE:%.*]]
; CHECK:       loop.preheader:
; CHECK-NEXT:    br label [[LOOP:%.*]]
; CHECK:       loop:
; CHECK-NEXT:    [[IV:%.*]] = phi i32 [ [[IV_INC:%.*]], [[BE:%.*]] ], [ 0, [[LOOP_PREHEADER]] ]
; CHECK-NEXT:    [[IV_INC]] = add nuw nsw i32 [[IV]], 1
; CHECK-NEXT:    br i1 true, label [[BE]], label [[LEAVE_LOOPEXIT:%.*]]
; CHECK:       be:
; CHECK-NEXT:    call void @side_effect()
; CHECK-NEXT:    [[EXITCOND:%.*]] = icmp ne i32 [[IV_INC]], [[LIM]]
; CHECK-NEXT:    br i1 [[EXITCOND]], label [[LOOP]], label [[LEAVE_LOOPEXIT]]
; CHECK:       leave.loopexit:
; CHECK-NEXT:    br label [[LEAVE]]
; CHECK:       leave:
; CHECK-NEXT:    ret void
;
entry:
  %length = load i32, i32* %length.ptr, !range !0
  %lim = sub i32 %length, 1
  %entry.cond = icmp sgt i32 %length, 1
  br i1 %entry.cond, label %loop, label %leave

loop:
  %iv = phi i32 [ 0, %entry ], [ %iv.inc, %be ]
  %iv.inc = add i32 %iv, 1
  %range.check = icmp slt i32 %iv, %length
  br i1 %range.check, label %be, label %leave

be:
  call void @side_effect()
  %be.cond = icmp slt i32 %iv.inc, %lim
  br i1 %be.cond, label %loop, label %leave

leave:
  ret void
}

; This checks that the backedge condition, (I + 1) < Length - 1 implies
; (I + 1) < Length
define void @func_22(i32* %length.ptr) {
; CHECK-LABEL: @func_22(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    [[LENGTH:%.*]] = load i32, i32* [[LENGTH_PTR:%.*]], align 4, !range [[RNG0]]
; CHECK-NEXT:    [[ENTRY_COND:%.*]] = icmp sgt i32 [[LENGTH]], 1
; CHECK-NEXT:    br i1 [[ENTRY_COND]], label [[LOOP_PREHEADER:%.*]], label [[LEAVE:%.*]]
; CHECK:       loop.preheader:
; CHECK-NEXT:    br label [[LOOP:%.*]]
; CHECK:       loop:
; CHECK-NEXT:    [[IV:%.*]] = phi i32 [ [[IV_INC:%.*]], [[BE:%.*]] ], [ 0, [[LOOP_PREHEADER]] ]
; CHECK-NEXT:    [[IV_INC]] = add nuw nsw i32 [[IV]], 1
; CHECK-NEXT:    br i1 true, label [[BE]], label [[LEAVE_LOOPEXIT:%.*]]
; CHECK:       be:
; CHECK-NEXT:    call void @side_effect()
; CHECK-NEXT:    [[EXITCOND:%.*]] = icmp ne i32 [[IV_INC]], [[LENGTH]]
; CHECK-NEXT:    br i1 [[EXITCOND]], label [[LOOP]], label [[LEAVE_LOOPEXIT]]
; CHECK:       leave.loopexit:
; CHECK-NEXT:    br label [[LEAVE]]
; CHECK:       leave:
; CHECK-NEXT:    ret void
;
entry:
  %length = load i32, i32* %length.ptr, !range !0
  %lim = sub i32 %length, 1
  %entry.cond = icmp sgt i32 %length, 1
  br i1 %entry.cond, label %loop, label %leave

loop:
  %iv = phi i32 [ 0, %entry ], [ %iv.inc, %be ]
  %iv.inc = add i32 %iv, 1
  %range.check = icmp sle i32 %iv, %length
  br i1 %range.check, label %be, label %leave

be:
  call void @side_effect()
  %be.cond = icmp sle i32 %iv.inc, %lim
  br i1 %be.cond, label %loop, label %leave

leave:
  ret void
}

define void @func_23(i32* %length.ptr) {
; CHECK-LABEL: @func_23(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    [[LENGTH:%.*]] = load i32, i32* [[LENGTH_PTR:%.*]], align 4, !range [[RNG0]]
; CHECK-NEXT:    [[ENTRY_COND:%.*]] = icmp ult i32 4, [[LENGTH]]
; CHECK-NEXT:    br i1 [[ENTRY_COND]], label [[LOOP_PREHEADER:%.*]], label [[LEAVE:%.*]]
; CHECK:       loop.preheader:
; CHECK-NEXT:    br label [[LOOP:%.*]]
; CHECK:       loop:
; CHECK-NEXT:    [[IV:%.*]] = phi i32 [ [[IV_INC:%.*]], [[BE:%.*]] ], [ 4, [[LOOP_PREHEADER]] ]
; CHECK-NEXT:    [[IV_INC]] = add nuw nsw i32 [[IV]], 1
; CHECK-NEXT:    br i1 true, label [[BE]], label [[LEAVE_LOOPEXIT:%.*]]
; CHECK:       be:
; CHECK-NEXT:    call void @side_effect()
; CHECK-NEXT:    [[EXITCOND:%.*]] = icmp ne i32 [[IV_INC]], [[LENGTH]]
; CHECK-NEXT:    br i1 [[EXITCOND]], label [[LOOP]], label [[LEAVE_LOOPEXIT]]
; CHECK:       leave.loopexit:
; CHECK-NEXT:    br label [[LEAVE]]
; CHECK:       leave:
; CHECK-NEXT:    ret void
;
entry:
  %length = load i32, i32* %length.ptr, !range !0
  %entry.cond = icmp ult i32 4, %length
  br i1 %entry.cond, label %loop, label %leave

loop:
  %iv = phi i32 [ 4, %entry ], [ %iv.inc, %be ]
  %iv.inc = add i32 %iv, 1
  %range.check = icmp slt i32 %iv, %length
  br i1 %range.check, label %be, label %leave

be:
  call void @side_effect()
  %be.cond = icmp slt i32 %iv.inc, %length
  br i1 %be.cond, label %loop, label %leave

leave:
  ret void
}

define void @func_24(i32* %init.ptr) {
; CHECK-LABEL: @func_24(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    [[INIT:%.*]] = load i32, i32* [[INIT_PTR:%.*]], align 4, !range [[RNG0]]
; CHECK-NEXT:    [[ENTRY_COND:%.*]] = icmp ugt i32 [[INIT]], 4
; CHECK-NEXT:    br i1 [[ENTRY_COND]], label [[LOOP_PREHEADER:%.*]], label [[LEAVE:%.*]]
; CHECK:       loop.preheader:
; CHECK-NEXT:    br label [[LOOP:%.*]]
; CHECK:       loop:
; CHECK-NEXT:    [[IV:%.*]] = phi i32 [ [[IV_DEC:%.*]], [[BE:%.*]] ], [ [[INIT]], [[LOOP_PREHEADER]] ]
; CHECK-NEXT:    [[IV_DEC]] = add nsw i32 [[IV]], -1
; CHECK-NEXT:    br i1 true, label [[BE]], label [[LEAVE_LOOPEXIT:%.*]]
; CHECK:       be:
; CHECK-NEXT:    call void @side_effect()
; CHECK-NEXT:    [[BE_COND:%.*]] = icmp sgt i32 [[IV_DEC]], 4
; CHECK-NEXT:    br i1 [[BE_COND]], label [[LOOP]], label [[LEAVE_LOOPEXIT]]
; CHECK:       leave.loopexit:
; CHECK-NEXT:    br label [[LEAVE]]
; CHECK:       leave:
; CHECK-NEXT:    ret void
;
entry:
  %init = load i32, i32* %init.ptr, !range !0
  %entry.cond = icmp ugt i32 %init, 4
  br i1 %entry.cond, label %loop, label %leave

loop:
  %iv = phi i32 [ %init, %entry ], [ %iv.dec, %be ]
  %iv.dec = add i32 %iv, -1
  %range.check = icmp sgt i32 %iv, 4
  br i1 %range.check, label %be, label %leave

be:
  call void @side_effect()
  %be.cond = icmp sgt i32 %iv.dec, 4
  br i1 %be.cond, label %loop, label %leave

leave:
  ret void
}

declare i1 @cond_func()

define i32 @func_25(i32 %start) {
; CHECK-LABEL: @func_25(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    br label [[LOOP:%.*]]
; CHECK:       loop:
; CHECK-NEXT:    [[IV:%.*]] = phi i32 [ [[START:%.*]], [[ENTRY:%.*]] ], [ [[IV_NEXT:%.*]], [[BACKEDGE:%.*]] ]
; CHECK-NEXT:    [[C1:%.*]] = icmp ne i32 [[IV]], 0
; CHECK-NEXT:    br i1 [[C1]], label [[CHECKED_1:%.*]], label [[FAIL:%.*]]
; CHECK:       checked.1:
; CHECK-NEXT:    [[C2:%.*]] = icmp ne i32 [[IV]], 0
; CHECK-NEXT:    br i1 [[C2]], label [[CHECKED_2:%.*]], label [[FAIL]]
; CHECK:       checked.2:
; CHECK-NEXT:    [[C3:%.*]] = icmp ne i32 [[IV]], 0
; CHECK-NEXT:    br i1 [[C3]], label [[BACKEDGE]], label [[FAIL]]
; CHECK:       backedge:
; CHECK-NEXT:    [[IV_NEXT]] = add i32 [[IV]], 758394
; CHECK-NEXT:    [[LOOP_COND:%.*]] = call i1 @cond_func()
; CHECK-NEXT:    br i1 [[LOOP_COND]], label [[LOOP]], label [[EXIT:%.*]]
; CHECK:       fail:
; CHECK-NEXT:    unreachable
; CHECK:       exit:
; CHECK-NEXT:    [[IV_LCSSA1:%.*]] = phi i32 [ [[IV]], [[BACKEDGE]] ]
; CHECK-NEXT:    ret i32 [[IV_LCSSA1]]
;
entry:
  br label %loop

loop:
  %iv = phi i32 [%start, %entry], [%iv.next, %backedge]
  %c1 = icmp ne i32 %iv, 0
  br i1 %c1, label %checked.1, label %fail

checked.1:
  %c2 = icmp ne i32 %iv, 0
  br i1 %c2, label %checked.2, label %fail

checked.2:
  %c3 = icmp ne i32 %iv, 0
  br i1 %c3, label %backedge, label %fail

backedge:
  %iv.next = add i32 %iv, 758394
  %loop.cond = call i1 @cond_func()
  br i1 %loop.cond, label %loop, label %exit

fail:
  unreachable

exit:
  ret i32 %iv
}

define i32 @func_26(i32 %start) {
; CHECK-LABEL: @func_26(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    br label [[LOOP:%.*]]
; CHECK:       loop:
; CHECK-NEXT:    [[IV:%.*]] = phi i32 [ [[START:%.*]], [[ENTRY:%.*]] ], [ [[IV_NEXT:%.*]], [[BACKEDGE:%.*]] ]
; CHECK-NEXT:    [[C1:%.*]] = icmp slt i32 [[IV]], 0
; CHECK-NEXT:    br i1 [[C1]], label [[CHECKED_1:%.*]], label [[FAIL:%.*]]
; CHECK:       checked.1:
; CHECK-NEXT:    [[C2:%.*]] = icmp slt i32 [[IV]], 1
; CHECK-NEXT:    br i1 [[C2]], label [[CHECKED_2:%.*]], label [[FAIL]]
; CHECK:       checked.2:
; CHECK-NEXT:    [[C3:%.*]] = icmp slt i32 [[IV]], 2
; CHECK-NEXT:    br i1 [[C3]], label [[BACKEDGE]], label [[FAIL]]
; CHECK:       backedge:
; CHECK-NEXT:    [[IV_NEXT]] = add i32 [[IV]], 758394
; CHECK-NEXT:    [[LOOP_COND:%.*]] = call i1 @cond_func()
; CHECK-NEXT:    br i1 [[LOOP_COND]], label [[LOOP]], label [[EXIT:%.*]]
; CHECK:       fail:
; CHECK-NEXT:    unreachable
; CHECK:       exit:
; CHECK-NEXT:    [[IV_LCSSA1:%.*]] = phi i32 [ [[IV]], [[BACKEDGE]] ]
; CHECK-NEXT:    ret i32 [[IV_LCSSA1]]
;
entry:
  br label %loop

loop:
  %iv = phi i32 [%start, %entry], [%iv.next, %backedge]
  %c1 = icmp slt i32 %iv, 0
  br i1 %c1, label %checked.1, label %fail

checked.1:
  %c2 = icmp slt i32 %iv, 1
  br i1 %c2, label %checked.2, label %fail

checked.2:
  %c3 = icmp slt i32 %iv, 2
  br i1 %c3, label %backedge, label %fail

backedge:
  %iv.next = add i32 %iv, 758394
  %loop.cond = call i1 @cond_func()
  br i1 %loop.cond, label %loop, label %exit

fail:
  unreachable

exit:
  ret i32 %iv
}


!0 = !{i32 0, i32 2147483647}
