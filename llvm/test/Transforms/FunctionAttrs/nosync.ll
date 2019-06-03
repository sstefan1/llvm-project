; RUN: opt -functionattrs -S < %s | FileCheck %s
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"

; Test cases designet for the "nosync" function attribute.
; FIXME's are used to indicate problems and missing attributes.

; struct RT {
;   char A;
;   int B[10][20];
;   char C;
; };
; struct ST {
;   int X;
;   double Y;
;   struct RT Z;
; };
; 
; int *foo(struct ST *s) {
;   return &s[1].Z.B[5][13];
; }

; TEST 1
; attribute readnone implies "nosync"
%struct.RT = type { i8, [10 x [20 x i32]], i8 }
%struct.ST = type { i32, double, %struct.RT }

; FIXME: missing "nosync"
; CHECK Function Attrs: nounwind uwtable readnone optsize ssp
define i32* @foo(%struct.ST* %s) nounwind uwtable readnone optsize ssp {
entry:
  %arrayidx = getelementptr inbounds %struct.ST, %struct.ST* %s, i64 1, i32 2, i32 1, i64 5, i64 13
  ret i32* %arrayidx
} 

; TEST 2
; atomic load with monotonic ordering
; int load_monotonic(_Atomic int *num) {
;   int n = atomic_load_explicit(num, memory_order_relaxed);
;   return n;
; }
  
; FIXME: missing "nosync"
; CHECK: Function Attrs: norecurse nounwind uwtable
; CHECK-NEXT: define i32 @load_monotonic(i32* nocapture readonly)
define i32 @load_monotonic(i32* nocapture readonly) norecurse nounwind uwtable {
  %2 = load atomic i32, i32* %0 monotonic, align 4
  ret i32 %2
}


; TEST 3
; atomic store with monotonic ordering.
; void store_monotonic(_Atomic int *num) {
;   atomic_load_explicit(num, memory_order_relaxed);
; }

; FIXME: missing "nosync"
; CHECK: Function Attrs: norecurse nounwind uwtable
; CHECK-NEXT: define void @store_monotonic(i32* nocapture)
define void @store_monotonic(i32* nocapture) norecurse nounwind uwtable {
  store atomic i32 10, i32* %0 monotonic, align 4
  ret void
}

; TEST 4 - negative, should not deduce "nosync"
; atomic load with acquire ordering.
; int load_acquire(_Atomic int *num) {
;   int n = atomic_load_explicit(num, memory_order_acquire);
;   return n;
; }

; CHECK: Function Attrs: norecurse nounwind uwtable
; CHECK-NOT: nosync
; CHECK-NEXT: define i32 @load_acquire(i32* nocapture readonly)
define i32 @load_acquire(i32* nocapture readonly) norecurse nounwind uwtable {
  %2 = load atomic i32, i32* %0 acquire, align 4
  ret i32 %2
}

; TEST 5 - negative, should not deduce "nosync"
; atomic load with release ordering
; void load_release(_Atomic int *num) {
;   atomic_store_explicit(num, 10, memory_order_release);
; }

; CHECK: Function Attrs: norecurse nounwind uwtable
; CHECK-NOT: nosync
; CHECK-NEXT: define void @load_release(i32* nocapture)
define void @load_release(i32* nocapture) norecurse nounwind uwtable {
  store atomic i32 10, i32* %0 release, align 4
  ret void
}

; TEST 6 - negative, should not deduce "nosync"
; volatile store.
; void volatile_store(volatile int *num) {
;   *num = 14;
; }

; CHECK: Function Attrs: norecurse nounwind uwtable
; CHECK-NOT: nosync
; CHECK-NEXT: define void @volatile_store(i32*)
define void @volatile_store(i32*) norecurse nounwind uwtable {
  ;store volatile i32 14, i32* %0, align 4, !tbaa !2
  store volatile i32 14, i32* %0, align 4
  ret void
}

; TEST 7 - negative, should not deduce "nosync"
; volatile load.
; int volatile_load(volatile int *num) {
;   int n = *num;
;   return n;
; }

; CHECK: Function Attrs: norecurse nounwind uwtable
; CHECK-NOT: nosync
; CHECK-NEXT: define i32 @volatile_load(i32*)
define i32 @volatile_load(i32*) norecurse nounwind uwtable {
  ;%2 = load volatile i32, i32* %0, align 4, !tbaa !2
  %2 = load volatile i32, i32* %0, align 4
  ret i32 %2
}

; TEST 8 
declare void @nosync_function() noinline nounwind uwtable

; FIXME: missing "nosync"
; CHECK: Function Attrs: noinline nounwind uwtable
; CHECK: define void @call_nosync_function()
define void @call_nosync_function() nounwind uwtable noinline {
  tail call void @nosync_function() noinline nounwind uwtable
  ret void
}

; TEST 9 - negative, should not deduce "nosync"
declare void @might_sync() noinline nounwind uwtable

; CHECK: Function Attrs: noinline nounwind uwtable
; CHECK-NOT: nosync
; CHECK: define void @call_might_sync()
define void @call_might_sync() nounwind uwtable noinline {
  tail call void @might_sync() noinline nounwind uwtable
  ret void
}

; TEST 10 - negative, should not deduce "nosync"
; volatile operation in same scc. Call volatile_load defined in TEST 7.

; CHECK: Function Attrs: noinline nounwind uwtable
; CHECK-NOT: nosync
; CHECK-NEXT: define i32 @scc1(i32*)
define i32 @scc1(i32*) noinline nounwind uwtable {
  tail call void @scc2(i32* %0);
  %val = tail call i32 @volatile_load(i32* %0);
  ret i32 %val;
}

; CHECK: Function Attrs: noinline nounwind uwtable
; CHECK-NOT: nosync
; CHECK-NEXT: define void @scc2(i32*)
define void @scc2(i32*) noinline nounwind uwtable {
  tail call i32 @scc1(i32* %0);
  ret void;
}
