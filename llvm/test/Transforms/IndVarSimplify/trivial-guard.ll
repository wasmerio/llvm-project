; NOTE: Assertions have been autogenerated by utils/update_test_checks.py
; RUN: opt -indvars -S < %s | FileCheck %s
; RUN: opt -passes=indvars -S < %s | FileCheck %s

declare i1 @cond()

define void @test_01(i32 %x) {
; CHECK-LABEL: @test_01(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    br i1 true, label [[LOOP_1_PREHEADER:%.*]], label [[LOOP_2_PREHEADER:%.*]]
; CHECK:       loop.2.preheader:
; CHECK-NEXT:    br label [[LOOP_2:%.*]]
; CHECK:       loop.1.preheader:
; CHECK-NEXT:    br label [[LOOP_1:%.*]]
; CHECK:       loop.1:
; CHECK-NEXT:    [[IV_1:%.*]] = phi i32 [ [[IV_NEXT_1:%.*]], [[GUARDED_1:%.*]] ], [ 0, [[LOOP_1_PREHEADER]] ]
; CHECK-NEXT:    [[CHECK_1:%.*]] = icmp slt i32 [[IV_1]], [[X:%.*]]
; CHECK-NEXT:    br i1 [[CHECK_1]], label [[GUARDED_1]], label [[FAIL_LOOPEXIT:%.*]]
; CHECK:       guarded.1:
; CHECK-NEXT:    [[IV_NEXT_1]] = add nuw i32 [[IV_1]], 1
; CHECK-NEXT:    [[LOOP_COND_1:%.*]] = call i1 @cond()
; CHECK-NEXT:    br i1 [[LOOP_COND_1]], label [[LOOP_1]], label [[EXIT_LOOPEXIT:%.*]]
; CHECK:       loop.2:
; CHECK-NEXT:    [[IV_2:%.*]] = phi i32 [ [[IV_NEXT_2:%.*]], [[GUARDED_2:%.*]] ], [ 0, [[LOOP_2_PREHEADER]] ]
; CHECK-NEXT:    [[CHECK_2:%.*]] = icmp slt i32 [[IV_2]], [[X]]
; CHECK-NEXT:    br i1 [[CHECK_2]], label [[GUARDED_2]], label [[FAIL_LOOPEXIT1:%.*]]
; CHECK:       guarded.2:
; CHECK-NEXT:    [[IV_NEXT_2]] = add nuw i32 [[IV_2]], 1
; CHECK-NEXT:    [[LOOP_COND_2:%.*]] = call i1 @cond()
; CHECK-NEXT:    br i1 [[LOOP_COND_2]], label [[LOOP_2]], label [[EXIT_LOOPEXIT2:%.*]]
; CHECK:       exit.loopexit:
; CHECK-NEXT:    br label [[EXIT:%.*]]
; CHECK:       exit.loopexit2:
; CHECK-NEXT:    br label [[EXIT]]
; CHECK:       exit:
; CHECK-NEXT:    ret void
; CHECK:       fail.loopexit:
; CHECK-NEXT:    br label [[FAIL:%.*]]
; CHECK:       fail.loopexit1:
; CHECK-NEXT:    br label [[FAIL]]
; CHECK:       fail:
; CHECK-NEXT:    unreachable
;
entry:
  br i1 true, label %loop.1, label %loop.2

loop.1:
  %iv.1 = phi i32 [0, %entry], [%iv.next.1, %guarded.1]
  %check.1 = icmp slt i32 %iv.1, %x
  br i1 %check.1, label %guarded.1, label %fail

guarded.1:
  %iv.next.1 = add i32 %iv.1, 1
  %loop.cond.1 = call i1 @cond()
  br i1 %loop.cond.1, label %loop.1, label %exit

loop.2:
  %iv.2 = phi i32 [0, %entry], [%iv.next.2, %guarded.2]
  %check.2 = icmp slt i32 %iv.2, %x
  br i1 %check.2, label %guarded.2, label %fail

guarded.2:
  %iv.next.2 = add i32 %iv.2, 1
  %loop.cond.2 = call i1 @cond()
  br i1 %loop.cond.2, label %loop.2, label %exit

exit:
  ret void

fail:
  unreachable
}

define void @test_02(i32 %x) {
; CHECK-LABEL: @test_02(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    br i1 false, label [[LOOP_1_PREHEADER:%.*]], label [[LOOP_2_PREHEADER:%.*]]
; CHECK:       loop.2.preheader:
; CHECK-NEXT:    br label [[LOOP_2:%.*]]
; CHECK:       loop.1.preheader:
; CHECK-NEXT:    br label [[LOOP_1:%.*]]
; CHECK:       loop.1:
; CHECK-NEXT:    [[IV_1:%.*]] = phi i32 [ [[IV_NEXT_1:%.*]], [[GUARDED_1:%.*]] ], [ 0, [[LOOP_1_PREHEADER]] ]
; CHECK-NEXT:    [[CHECK_1:%.*]] = icmp slt i32 [[IV_1]], [[X:%.*]]
; CHECK-NEXT:    br i1 [[CHECK_1]], label [[GUARDED_1]], label [[FAIL_LOOPEXIT:%.*]]
; CHECK:       guarded.1:
; CHECK-NEXT:    [[IV_NEXT_1]] = add nuw i32 [[IV_1]], 1
; CHECK-NEXT:    [[LOOP_COND_1:%.*]] = call i1 @cond()
; CHECK-NEXT:    br i1 [[LOOP_COND_1]], label [[LOOP_1]], label [[EXIT_LOOPEXIT:%.*]]
; CHECK:       loop.2:
; CHECK-NEXT:    [[IV_2:%.*]] = phi i32 [ [[IV_NEXT_2:%.*]], [[GUARDED_2:%.*]] ], [ 0, [[LOOP_2_PREHEADER]] ]
; CHECK-NEXT:    [[CHECK_2:%.*]] = icmp slt i32 [[IV_2]], [[X]]
; CHECK-NEXT:    br i1 [[CHECK_2]], label [[GUARDED_2]], label [[FAIL_LOOPEXIT1:%.*]]
; CHECK:       guarded.2:
; CHECK-NEXT:    [[IV_NEXT_2]] = add nuw i32 [[IV_2]], 1
; CHECK-NEXT:    [[LOOP_COND_2:%.*]] = call i1 @cond()
; CHECK-NEXT:    br i1 [[LOOP_COND_2]], label [[LOOP_2]], label [[EXIT_LOOPEXIT2:%.*]]
; CHECK:       exit.loopexit:
; CHECK-NEXT:    br label [[EXIT:%.*]]
; CHECK:       exit.loopexit2:
; CHECK-NEXT:    br label [[EXIT]]
; CHECK:       exit:
; CHECK-NEXT:    ret void
; CHECK:       fail.loopexit:
; CHECK-NEXT:    br label [[FAIL:%.*]]
; CHECK:       fail.loopexit1:
; CHECK-NEXT:    br label [[FAIL]]
; CHECK:       fail:
; CHECK-NEXT:    unreachable
;
entry:
  br i1 false, label %loop.1, label %loop.2

loop.1:
  %iv.1 = phi i32 [0, %entry], [%iv.next.1, %guarded.1]
  %check.1 = icmp slt i32 %iv.1, %x
  br i1 %check.1, label %guarded.1, label %fail

guarded.1:
  %iv.next.1 = add i32 %iv.1, 1
  %loop.cond.1 = call i1 @cond()
  br i1 %loop.cond.1, label %loop.1, label %exit

loop.2:
  %iv.2 = phi i32 [0, %entry], [%iv.next.2, %guarded.2]
  %check.2 = icmp slt i32 %iv.2, %x
  br i1 %check.2, label %guarded.2, label %fail

guarded.2:
  %iv.next.2 = add i32 %iv.2, 1
  %loop.cond.2 = call i1 @cond()
  br i1 %loop.cond.2, label %loop.2, label %exit

exit:
  ret void

fail:
  unreachable
}
