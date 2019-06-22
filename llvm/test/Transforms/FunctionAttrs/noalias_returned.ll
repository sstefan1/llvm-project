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

; TEST 2
; call noalias function in return instruction.
; CHECK: define "noalias" i8* @return_noalias()
define i8* @return_noalias(){
  %1 = tail call noalias i8* @malloc(i64 4)
  ret i8* %1
}

declare i8* @alias()

; TEST 3
; CHECK: define i8* @call_alias()
; CHECK-NOT: "noalias"
define i8* @call_alias(){
  %1 = tail call i8* @alias()
  ret i8* %1
}

; TEST 4
; void *baz();
; void *foo(int a);
;
; void *bar()  {
;   foo(0);
;    return baz();
; }
;
; void *foo(int a)  {
;   if (a)
;   bar();
;   return malloc(4);
; }

; CHECK: define i8* @bar()
define i8* @bar() nounwind uwtable {
  %1 = tail call i8* (...) @baz()
  ret i8* %1
}

; CHECK: define "noalias" i8* @foo(i32)
define i8* @foo(i32) nounwind uwtable {
  %2 = icmp eq i32 %0, 0
  br i1 %2, label %5, label %3

3:                                                ; preds = %1
  %4 = tail call i8* (...) @baz()
  br label %5

5:                                                ; preds = %1, %3
  %6 = tail call noalias i8* @malloc(i64 4)
  ret i8* %6
}

declare i8* @baz(...) nounwind uwtable

; TEST 5

define i8* @getter() {
  ret i8* @G
}

define i8* @calle1(){
  %1 = call i8* @getter()
  ret i8* %1 
}

define i8* @calle2(){
  %1 = tail call i8* @getter()
  ret i8* %1 
}

; %1 & %2 alias
define void entry(){
  %1 = tail call i8* @calle1()
  %2 = tail call i8* @calee2()
}

