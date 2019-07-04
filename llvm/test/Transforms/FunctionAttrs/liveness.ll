; RUN: opt -attributor --attributor-disable=false -S < %s | FileCheck %s

declare void @no_return_call() noreturn

declare void @normal_call()

; TEST 1: cond.true is dead, but cond.end is not, since cond.false is live

; This is just an example. For example we can put a sync call in a
; dead block and check if it is deduced.

define i32 @dead_block_present(i32 %a) #0 {
entry:
  %cmp = icmp eq i32 %a, 0
  br i1 %cmp, label %cond.true, label %cond.false

cond.true:                                        ; preds = %entry
  call void @no_return_call()
  %call = call i32 @endless_loop(i32 %a)
  br label %cond.end

cond.false:                                       ; preds = %entry
  call void @normal_call()
  %call1 = call i32 @srec16(i32 %a)
  br label %cond.end

cond.end:                                         ; preds = %cond.false, %cond.true
  %cond = phi i32 [ %call, %cond.true ], [ %call1, %cond.false ]
  ret i32 %cond
}

; TEST 2: both cond.true and cond.false are dead, therfore cond.end is dead as well.

define i32 @all_live(i32 %a) #0 {
entry:
  %cmp = icmp eq i32 %a, 0
  br i1 %cmp, label %cond.true, label %cond.false

cond.true:                                        ; preds = %entry
  call void @no_return_call()
  %call = call i32 @endless_loop(i32 %a)
  br label %cond.end

cond.false:                                       ; preds = %entry
  call void @no_return_call()
  %call1 = call i32 @srec16(i32 %a)
  br label %cond.end

cond.end:                                         ; preds = %cond.false, %cond.true
  %cond = phi i32 [ %call, %cond.true ], [ %call1, %cond.false ]
  ret i32 %cond
}
