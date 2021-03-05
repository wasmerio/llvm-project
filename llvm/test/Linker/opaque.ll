; RUN: llvm-link %p/opaque.ll %p/Inputs/opaque.ll -S -o - | FileCheck %s
; RUN: llvm-link --context-each-input %p/opaque.ll %p/Inputs/opaque.ll -S -o - | FileCheck %s

; CHECK-DAG: %A =   type {}
; CHECK-DAG: %B =   type { %C, %C, %B* }
; CHECK-DAG: %B.[[ID:[0-9]+]] = type { %D, %E, %B.[[ID]]* }
; CHECK-DAG: %C =   type { %A }
; CHECK-DAG: %D =   type { %E }
; CHECK-DAG: %E =   type opaque

; CHECK-DAG: @g1 = external global %B
; CHECK-DAG: @g2 = external global %A
; CHECK-DAG: @g3 = external global %B.[[ID]]

; CHECK-DAG: getelementptr %A, %A* null, i32 0

%A = type opaque
%B = type { %C, %C, %B* }

%C = type { %A }

@g1 = external global %B

define %B* @use_g1() {
  ret %B* @g1
}
