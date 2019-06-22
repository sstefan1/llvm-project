; RUN: opt -functionattrs -S < %s | FileCheck %s --check-prefix=FNATTR
; RUN: opt -attributor -S < %s | FileCheck %s --check-prefix=ATTRIBUTOR
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"

; Test cases designet for the nosync function attribute.
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
; attribute readnone implies nosync
%struct.RT = type { i8, [10 x [20 x i32]], i8 }
%struct.ST = type { i32, double, %struct.RT }

; FNATTR: Function Attrs: norecurse nounwind optsize readnone ssp uwtable
; FNATTR-NEXT: define nonnull i32* @foo(%struct.ST* readnone %s)
; ATTRIBUTOR: Function Attrs: nosync nounwind optsize readnone ssp uwtable
; ATTRIBUTOR-NEXT: define i32* @foo(%struct.ST* %s)
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

; FNATTR: Function Attrs: norecurse nounwind uwtable
; FNATTR-NEXT: define i32 @load_monotonic(i32* nocapture readonly)
; ATTRIBUTOR: Function Attrs: norecurse nosync nounwind uwtable
; ATTRIBUTOR-NEXT: define i32 @load_monotonic(i32* nocapture readonly)
define i32 @load_monotonic(i32* nocapture readonly) norecurse nounwind uwtable {
  %2 = load atomic i32, i32* %0 monotonic, align 4
  ret i32 %2
}


; TEST 3
; atomic store with monotonic ordering.
; void store_monotonic(_Atomic int *num) {
;   atomic_load_explicit(num, memory_order_relaxed);
; }

; FNATTR: Function Attrs: norecurse nounwind uwtable
; FNATTR-NEXT: define void @store_monotonic(i32* nocapture)
; ATTRIBUTOR: Function Attrs: norecurse nosync nounwind uwtable
; ATTRIBUTOR-NEXT: define void @store_monotonic(i32* nocapture)
define void @store_monotonic(i32* nocapture) norecurse nounwind uwtable {
  store atomic i32 10, i32* %0 monotonic, align 4
  ret void
}

; TEST 4 - negative, should not deduce nosync
; atomic load with acquire ordering.
; int load_acquire(_Atomic int *num) {
;   int n = atomic_load_explicit(num, memory_order_acquire);
;   return n;
; }

; FNATTR: Function Attrs: norecurse nounwind uwtable
; FNATTR-NEXT: define i32 @load_acquire(i32* nocapture readonly)
; ATTRIBUTOR: Function Attrs: norecurse nounwind uwtable
; ATTRIBUTOR-NOT: nosync
; ATTRIBUTOR-NEXT: define i32 @load_acquire(i32* nocapture readonly)
define i32 @load_acquire(i32* nocapture readonly) norecurse nounwind uwtable {
  %2 = load atomic i32, i32* %0 acquire, align 4
  ret i32 %2
}

; TEST 5 - negative, should not deduce nosync
; atomic load with release ordering
; void load_release(_Atomic int *num) {
;   atomic_store_explicit(num, 10, memory_order_release);
; }

; FNATTR: Function Attrs: norecurse nounwind uwtable
; FNATTR-NEXT: define void @load_release(i32* nocapture)
; ATTRIBUTOR: Function Attrs: norecurse nounwind uwtable
; ATTRIBUTOR-NOT: nosync
; ATTRIBUTOR-NEXT: define void @load_release(i32* nocapture)
define void @load_release(i32* nocapture) norecurse nounwind uwtable {
  store atomic i32 10, i32* %0 release, align 4
  ret void
}

; TEST 6 - negative, should not deduce nosync
; volatile store.
; void volatile_store(volatile int *num) {
;   *num = 14;
; }

; FNATTR: Function Attrs: norecurse nounwind uwtable
; FNATTR-NEXT: define void @volatile_store(i32*)
; ATTRIBUTOR: Function Attrs: norecurse nounwind uwtable
; ATTRIBUTOR-NOT: nosync
; ATTRIBUTOR-NEXT: define void @volatile_store(i32*)
define void @volatile_store(i32*) norecurse nounwind uwtable {
  store volatile i32 14, i32* %0, align 4
  ret void
}

; TEST 7 - negative, should not deduce nosync
; volatile load.
; int volatile_load(volatile int *num) {
;   int n = *num;
;   return n;
; }

; FNATTR: Function Attrs: norecurse nounwind uwtable
; FNATTR-NEXT: define i32 @volatile_load(i32*)
; ATTRIBUTOR: Function Attrs: norecurse nounwind uwtable
; ATTRIBUTOR-NOT: nosync
; ATTRIBUTOR-NEXT: define i32 @volatile_load(i32*)
define i32 @volatile_load(i32*) norecurse nounwind uwtable {
  %2 = load volatile i32, i32* %0, align 4
  ret i32 %2
}

; TEST 8

; FNATTR: Function Attrs: noinline nosync nounwind uwtable
; FNATTR-NEXT: declare void @nosync_function()
; ATTRIBUTOR: Function Attrs: noinline nosync nounwind uwtable
; ATTRIBUTOR-NEXT: declare void @nosync_function()
declare void @nosync_function() noinline nounwind uwtable nosync

; FNATTR: Function Attrs: noinline nounwind uwtable
; FNATTR-NEXT: define void @call_nosync_function()
; ATTRIBUTOR: Function Attrs: noinline nosync nounwind uwtable
; ATTRIBUTOR-next: define void @call_nosync_function()
define void @call_nosync_function() nounwind uwtable noinline {
  tail call void @nosync_function() noinline nounwind uwtable
  ret void
}

; TEST 9 - negative, should not deduce nosync

; FNATTR: Function Attrs: noinline nounwind uwtable
; FNATTR-NEXT: declare void @might_sync()
; ATTRIBUTOR: Function Attrs: noinline nounwind uwtable
; ATTRIBUTOR-NEXT: declare void @might_sync()
declare void @might_sync() noinline nounwind uwtable

; FNATTR: Function Attrs: noinline nounwind uwtable
; FNATTR-NEXT: define void @call_might_sync()
; ATTRIBUTOR: Function Attrs: noinline nounwind uwtable
; ATTRIBUTOR-NOT: nosync
; ATTRIBUTOR-NEXT: define void @call_might_sync()
define void @call_might_sync() nounwind uwtable noinline {
  tail call void @might_sync() noinline nounwind uwtable
  ret void
}

; TEST 10 - negative, should not deduce nosync
; volatile operation in same scc. Call volatile_load defined in TEST 7.

; FNATTR: Function Attrs: noinline nounwind uwtable
; FNATTR-NEXT: define i32 @scc1(i32*)
; ATTRIBUTOR: Function Attrs: noinline nounwind uwtable
; ATTRIBUTOR-NOT: nosync
; ATTRIBUTOR-NEXT: define i32 @scc1(i32*)
define i32 @scc1(i32*) noinline nounwind uwtable {
  tail call void @scc2(i32* %0);
  %val = tail call i32 @volatile_load(i32* %0);
  ret i32 %val;
}

; FNATTR: Function Attrs: noinline nounwind uwtable
; FNATTR-NEXT: define void @scc2(i32*)
; ATTRIBUTOR: Function Attrs: noinline nounwind uwtable
; ATTRIBUTOR-NOT: nosync
; ATTRIBUTOR-NEXT: define void @scc2(i32*)
define void @scc2(i32*) noinline nounwind uwtable {
  tail call i32 @scc1(i32* %0);
  ret void;
}

; TEST 11 - fences, negative
;
; void foo1(int *a, std::atomic<bool> flag){
;   *a = 100;
;   atomic_thread_fence(std::memory_order_release);
;   flag.store(true, std::memory_order_relaxed);
; }
;
; void bar(int *a, std::atomic<bool> flag){
;   while(!flag.load(std::memory_order_relaxed))
;     ;
;
;   atomic_thread_fence(std::memory_order_acquire);
;   int b = *a;
; }

%"struct.std::atomic" = type { %"struct.std::__atomic_base" }
%"struct.std::__atomic_base" = type { i8 }

; FNATTR: Function Attrs: norecurse nounwind
; FNATTR-NEXT: define void @foo1(i32* nocapture, %"struct.std::atomic"* nocapture)
; ATTRIBUTOR-NOT: nosync
; ATTRIBUTOR: define void @foo1(i32*, %"struct.std::atomic"*)
define void @foo1(i32*, %"struct.std::atomic"*) {
  store i32 100, i32* %0, align 4
  fence release
  %3 = getelementptr inbounds %"struct.std::atomic", %"struct.std::atomic"* %1, i64 0, i32 0, i32 0
  store atomic i8 1, i8* %3 monotonic, align 1
  ret void
}

; FNATTR: Function Attrs: norecurse nounwind
; FNATTR-NEXT: define void @bar(i32* nocapture readnone, %"struct.std::atomic"* nocapture readonly)
; ATTRIBUTOR-NOT: nosync
; ATTRIBUTOR: define void @bar(i32*, %"struct.std::atomic"*)
define void @bar(i32 *, %"struct.std::atomic"*) {
  %3 = getelementptr inbounds %"struct.std::atomic", %"struct.std::atomic"* %1, i64 0, i32 0, i32 0
  br label %4

4:                                                ; preds = %4, %2
  %5 = load atomic i8, i8* %3  monotonic, align 1
  %6 = and i8 %5, 1
  %7 = icmp eq i8 %6, 0
  br i1 %7, label %4, label %8

8:                                                ; preds = %4
  fence acquire
  ret void
}
