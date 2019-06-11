; RUN: opt -S -attributor -attributor-disable=false < %s | FileCheck %s

; TEST 1 - negative.

; void *G;
; void *foo(){
;   void *V = malloc(4);
;   G = V;
;   return V;
; }

@G = external global i8*

; CHECK: define i8* @foo()
define i8* @foo() {
  %1 = tail call noalias i8* @malloc(i64 4)
  store i8* %1, i8** @G, align 8
  ret i8* %1
}

declare noalias i8* @malloc(i64)
