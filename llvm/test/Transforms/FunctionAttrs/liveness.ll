; RUN: opt -attributor --attributor-disable=false -S < %s | FileCheck %s

declare void @no_return_call() noreturn

declare void @normal_call()

declare i32 @foo()

declare i32 @bar()

; TEST 1: cond.true is dead, but cond.end is not, since cond.false is live

; This is just an example. For example we can put a sync call in a
; dead block and check if it is deduced.

define i32 @dead_block_present(i32 %a) #0 {
entry:
  %cmp = icmp eq i32 %a, 0
  br i1 %cmp, label %cond.true, label %cond.false

cond.true:                                        ; preds = %entry
  call void @no_return_call()
  ; CHECK: unreachable
  %call = call i32 @foo()
  br label %cond.end

cond.false:                                       ; preds = %entry
  call void @normal_call()
  %call1 = call i32 @bar()
  br label %cond.end

cond.end:                                         ; preds = %cond.false, %cond.true
  %cond = phi i32 [ %call, %cond.true ], [ %call1, %cond.false ]
  ret i32 %cond
}

; TEST 2: both cond.true and cond.false are dead, therfore cond.end is dead as well.

define i32 @all_dead(i32 %a) #0 {
entry:
  %cmp = icmp eq i32 %a, 0
  br i1 %cmp, label %cond.true, label %cond.false

cond.true:                                        ; preds = %entry
  call void @no_return_call()
  ; CHECK: unreachable
  %call = call i32 @foo()
  br label %cond.end

cond.false:                                       ; preds = %entry
  call void @no_return_call()
  ; CHECK: unreachable
  %call1 = call i32 @bar()
  br label %cond.end

cond.end:                                         ; preds = %cond.false, %cond.true
  %cond = phi i32 [ %call, %cond.true ], [ %call1, %cond.false ]
  ret i32 %cond
}

; TEST 3: All blocks are live.

; CHECK: define i32 @all_live(i32 %a)
define i32 @all_live(i32 %a) #0 {
entry:
  %cmp = icmp eq i32 %a, 0
  br i1 %cmp, label %cond.true, label %cond.false

cond.true:                                        ; preds = %entry
  call void @normal_call()
  %call = call i32 @foo()
  br label %cond.end

cond.false:                                       ; preds = %entry
  call void @normal_call()
  %call1 = call i32 @bar()
  br label %cond.end

cond.end:                                         ; preds = %cond.false, %cond.true
  %cond = phi i32 [ %call, %cond.true ], [ %call1, %cond.false ]
  ret i32 %cond
}

; TEST 4: Undefined behvior
; FIXME: Should be able to detect undefined behavior.

; CHECK define @f(i32)
define i1 @f(i32) {
  %2 = add nsw i32 %0, 1
  %3 = icmp sgt i32 %2, %0
  ret i1 %3
}

define void @inf_loop() #0 {
entry:
  br label %while.body

while.body:                                       ; preds = %entry, %while.body
  br label %while.body
}

; TEST 5: Infinite loop.
; FIXME: Detect infloops, and mark affected blocks dead.

define i32 @test5(i32, i32) #0 {
  %3 = icmp sgt i32 %0, %1
  br i1 %3, label %cond.if, label %cond.elseif

cond.if:                                                ; preds = %2
  %4 = tail call i32 @bar()
  br label %cond.end

cond.elseif:                                                ; preds = %2
  call void @inf_loop()
  %5 = icmp slt i32 %0, %1
  br i1 %5, label %cond.end, label %cond.else

cond.else:                                                ; preds = %cond.elseif
  %6 = tail call i32 @foo()
  br label %cond.end

cond.end:                                               ; preds = %cond.if, %cond.else, %cond.elseif
  %7 = phi i32 [ %1, %cond.elseif ], [ 0, %cond.else ], [ 0, %cond.if ]
  ret i32 %7
}

define void @rec() #0 {
entry:
  call void @rec()
  ret void
}

; TEST 6: Recursion
; FIXME: everything after first block should be marked dead
; and unreachable should be put after call to @rec().

define i32 @test6(i32, i32) #0 {
  call void @rec()
  %3 = icmp sgt i32 %0, %1
  br i1 %3, label %cond.if, label %cond.elseif

cond.if:                                                ; preds = %2
  %4 = tail call i32 @bar()
  br label %cond.end

cond.elseif:                                                ; preds = %2
  call void @inf_loop()
  %5 = icmp slt i32 %0, %1
  br i1 %5, label %cond.end, label %cond.else

cond.else:                                                ; preds = %cond.elseif
  %6 = tail call i32 @foo()
  br label %cond.end

cond.end:                                               ; preds = %cond.if, %cond.else, %cond.elseif
  %7 = phi i32 [ %1, %cond.elseif ], [ 0, %cond.else ], [ 0, %cond.if ]
  ret i32 %7
}
