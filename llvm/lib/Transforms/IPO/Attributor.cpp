//===- Attributor.cpp - Module-wide attribute deduction -------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements an inter procedural pass that deduces and/or propagates
// attributes. This is done in an abstract interpretation style fixpoint
// iteration. See the Attributor.h file comment and the class descriptions in
// that file for more information.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/IPO/Attributor.h"

#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/CallGraphSCCPass.h"
#include "llvm/Analysis/GlobalsModRef.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

using namespace llvm;

#define DEBUG_TYPE "attributor"

STATISTIC(NumFnWithExactDefinition,
          "Number of function with exact definitions");
STATISTIC(NumFnWithoutExactDefinition,
          "Number of function without exact definitions");
STATISTIC(NumAttributesTimedOut,
          "Number of abstract attributes timed out before fixpoint");
STATISTIC(NumAttributesValidFixpoint,
          "Number of abstract attributes in a valid fixpoint state");
STATISTIC(NumAttributesManifested,
          "Number of abstract attributes manifested in IR");
STATISTIC(NumFnNoSync, "Number of functions marked nosync");

// TODO: Determine a good default value.
//
// In the LLVM-TS and SPEC2006, 32 seems to not induce compile time overheads
// (when run with the first 5 abstract attributes). The results also indicate
// that we never reach 32 iterations but always find a fixpoint sooner.
//
// This will become more evolved once we perform two interleaved fixpoint
// iterations: bottom-up and top-down.
static cl::opt<unsigned>
    MaxFixpointIterations("attributor-max-iterations", cl::Hidden,
                          cl::desc("Maximal number of fixpoint iterations."),
                          cl::init(32));

static cl::opt<bool> DisableAttributor(
    "attributor-disable", cl::Hidden,
    cl::desc("Disable the attributor inter-procedural deduction pass."),
    cl::init(false));

/// Logic operators for the change status enum class.
///
///{
ChangeStatus llvm::operator|(ChangeStatus l, ChangeStatus r) {
  return l == ChangeStatus::CHANGED ? l : r;
}
ChangeStatus llvm::operator&(ChangeStatus l, ChangeStatus r) {
  return l == ChangeStatus::UNCHANGED ? l : r;
}
///}

/// Simple state with integers encoding.
///
/// The interface ensures that the assumed bits are always a subset of the known
/// bits. Users can only add known bits and, except through adding known bits,
/// they can only remove assumed bits. This should guarantee monotoniticy and
/// thereby the existence of a fixpoint (if used corretly). The fixpoint is
/// reached when the assumed and known state/bits are equal. Users can
/// force/inidicate a fixpoint. If an optimistic one is indicated, the known
/// state will catch up with the assumed one, for a pessimistic fixpoint it is
/// the other way around.
struct IntegerState : public AbstractState {
  /// Undrlying integer type, we assume 32 bits to be enough.
  using base_t = uint32_t;

  /// Initialize the (best) state.
  IntegerState(base_t BestState = ~0) : Assumed(BestState) {}

  /// Return the worst possible representable state.
  static constexpr base_t getWorstState() { return 0; }

  /// See AbstractState::isValidState()
  /// NOTE: For now we simply pretend that the worst possible state is invalid.
  bool isValidState() const override { return Assumed != getWorstState(); }

  /// See AbstractState::isAtFixpoint()
  bool isAtFixpoint() const override { return Assumed == Known; }

  /// See AbstractState::indicateOptimisticFixpoint(...)
  void indicateOptimisticFixpoint() override { Known = Assumed; }

  /// See AbstractState::indicatePessimisticFixpoint(...)
  void indicatePessimisticFixpoint() override { Assumed = Known; }

  /// Return the known state encoding
  base_t getKnown() const { return Known; }

  /// Return the assumed state encoding.
  base_t getAssumed() const { return Assumed; }

  /// Return true if the bits set in \p BitsEncoding are "known bits".
  bool isKnown(base_t BitsEncoding) const {
    return (Known & BitsEncoding) == BitsEncoding;
  }

  /// Return true if the bits set in \p BitsEncoding are "assumed bits".
  bool isAssumed(base_t BitsEncoding) const {
    return (Assumed & BitsEncoding) == BitsEncoding;
  }

  /// Add the bits in \p BitsEncoding to the "known bits".
  IntegerState &addKnownBits(base_t Bits) {
    // Make sure we never miss any "known bits".
    Assumed |= Bits;
    Known |= Bits;
    return *this;
  }

  /// Remove the bits in \p BitsEncoding from the "assumed bits" if not known.
  IntegerState &removeAssumedBits(base_t BitsEncoding) {
    // Make sure we never loose any "known bits".
    Assumed = (Assumed & ~BitsEncoding) | Known;
    return *this;
  }

  /// Keep only "assumed bits" also set in \p BitsEncoding but all known ones.
  IntegerState &intersectAssumedBits(base_t BitsEncoding) {
    // Make sure we never loose any "known bits".
    Assumed = (Assumed & BitsEncoding) | Known;
    return *this;
  }

private:
  /// The known state encoding in an integer of type base_t.
  base_t Known = getWorstState();

  /// The assumed state encoding in an integer of type base_t.
  base_t Assumed;
};

/// Simple wrapper for a single bit (boolean) state.
struct BooleanState : public IntegerState {
  BooleanState() : IntegerState(1){};
};

/// Helper to adjust the statistics.
static void bookkeeping(AbstractAttribute::ManifestPosition MP,
                        const Attribute &Attr) {
  if (!AreStatisticsEnabled())
    return;

  if (Attr.isStringAttribute()) {
    StringRef StringAttr = Attr.getKindAsString();
    if (StringAttr == "nosync")
      NumFnNoSync++;
    return;
  }

  if (!Attr.isEnumAttribute())
    return;
  switch (Attr.getKindAsEnum()) {
  default:
    return;
  }
}

/// Helper to identify the correct offset into an attribute list.
static unsigned getAttrIndex(AbstractAttribute::ManifestPosition MP,
                             unsigned ArgNo = 0) {
  switch (MP) {
  case AbstractAttribute::MP_ARGUMENT:
  case AbstractAttribute::MP_CALL_SITE_ARGUMENT:
    return ArgNo + AttributeList::FirstArgIndex;
  case AbstractAttribute::MP_FUNCTION:
    return AttributeList::FunctionIndex;
  case AbstractAttribute::MP_RETURNED:
    return AttributeList::ReturnIndex;
  }
}

/// Return true if \p New is equal or worse than \p Old.
static bool isEqualOrWorse(const Attribute &New, const Attribute &Old) {
  if (!Old.isIntAttribute())
    return true;

  if (Old.getValueAsInt() >= New.getValueAsInt())
    return true;

  return false;
}

/// Return true if the information provided by \p Attr was added to the
/// attribute list \p Attrs. This is only the case if it was not already present
/// in \p Attrs at the position describe by \p MP and \p ArgNo.
static bool addIfNotExistent(LLVMContext &Ctx, const Attribute &Attr,
                             AttributeList &Attrs,
                             AbstractAttribute::ManifestPosition MP,
                             unsigned ArgNo = 0) {
  unsigned AttrIdx = getAttrIndex(MP, ArgNo);

  if (Attr.isEnumAttribute()) {
    Attribute::AttrKind Kind = Attr.getKindAsEnum();
    if (Attrs.hasAttribute(AttrIdx, Kind))
      if (isEqualOrWorse(Attr, Attrs.getAttribute(AttrIdx, Kind)))
        return false;
    Attrs = Attrs.addAttribute(Ctx, AttrIdx, Attr);
    return true;
  }
  if (Attr.isStringAttribute()) {
    StringRef Kind = Attr.getKindAsString();
    if (Attrs.hasAttribute(AttrIdx, Kind))
      if (isEqualOrWorse(Attr, Attrs.getAttribute(AttrIdx, Kind)))
        return false;
    Attrs = Attrs.addAttribute(Ctx, AttrIdx, Attr);
    return true;
  }

  llvm_unreachable("Expected enum or string attribute!");
}

ChangeStatus AbstractAttribute::update(Attributor &A) {
  ChangeStatus HasChanged = ChangeStatus::UNCHANGED;
  if (getState().isAtFixpoint())
    return HasChanged;

  LLVM_DEBUG(dbgs() << "[Attributor] Update: " << *this << "\n");

  HasChanged = updateImpl(A);

  LLVM_DEBUG(dbgs() << "[Attributor] Update " << HasChanged << " " << *this
                    << "\n");

  return HasChanged;
}

ChangeStatus AbstractAttribute::manifest(Attributor &A) {
  assert(getState().isValidState() &&
         "Attempted to manifest an invalid state!");
  assert(getAssociatedValue() &&
         "Attempted to manifest an attribute without associated value!");

  ChangeStatus HasChanged = ChangeStatus::UNCHANGED;
  SmallVector<Attribute, 4> DeducedAttrs;
  getDeducedAttributes(DeducedAttrs);

  Function &ScopeFn = getAnchorScope();
  LLVMContext &Ctx = ScopeFn.getContext();
  ManifestPosition MP = getManifestPosition();

  AttributeList Attrs;
  SmallVector<unsigned, 4> ArgNos;

  // In the following some generic code that will manifest attributes in
  // DeducedAttrs if they improve the current IR. Due to the different
  // annotation positions we use the underlying AttributeList interface.
  // Note that MP_CALL_SITE_ARGUMENT can annotate multiple locations.

  switch (MP) {
  case MP_ARGUMENT:
    ArgNos.push_back(cast<Argument>(getAssociatedValue())->getArgNo());
    Attrs = ScopeFn.getAttributes();
    break;
  case MP_FUNCTION:
  case MP_RETURNED:
    ArgNos.push_back(0);
    Attrs = ScopeFn.getAttributes();
    break;
  case MP_CALL_SITE_ARGUMENT: {
    CallSite CS(&getAnchoredValue());
    for (unsigned u = 0, e = CS.getNumArgOperands(); u != e; u++)
      if (CS.getArgOperand(u) == getAssociatedValue())
        ArgNos.push_back(u);
    Attrs = CS.getAttributes();
  }
  }

  for (const Attribute &Attr : DeducedAttrs) {
    for (unsigned ArgNo : ArgNos) {
      if (!addIfNotExistent(Ctx, Attr, Attrs, MP, ArgNo))
        continue;

      // Bookkeeping.
      HasChanged = ChangeStatus::CHANGED;
      bookkeeping(MP, Attr);
    }
  }

  if (HasChanged == ChangeStatus::UNCHANGED)
    return HasChanged;

  switch (MP) {
  case MP_ARGUMENT:
  case MP_FUNCTION:
  case MP_RETURNED:
    ScopeFn.setAttributes(Attrs);
    break;
  case MP_CALL_SITE_ARGUMENT:
    CallSite(&getAnchoredValue()).setAttributes(Attrs);
  }

  return HasChanged;
}

Function &AbstractAttribute::getAnchorScope() {
  Value &V = getAnchoredValue();
  if (isa<Function>(V))
    return cast<Function>(V);
  if (isa<Argument>(V))
    return *cast<Argument>(V).getParent();
  if (isa<Instruction>(V))
    return *cast<Instruction>(V).getFunction();
  llvm_unreachable("No scope for anchored value found!");
}

const Function &AbstractAttribute::getAnchorScope() const {
  return const_cast<AbstractAttribute *>(this)->getAnchorScope();
}

/// ------------------------ NoSync Function Attribute -------------------------

struct AANoSyncFunction : AbstractAttribute, BooleanState {

  AANoSyncFunction(Function &F, InformationCache &InfoCache)
      : AbstractAttribute(F, InfoCache) {}

  /// See AbstractAttribute::getState()
  /// {
  AbstractState &getState() override { return *this; }
  const AbstractState &getState() const override { return *this; }
  /// }

  /// See AbstractAttribute::getManifestPosition().
  virtual ManifestPosition getManifestPosition() const override {
    return MP_FUNCTION;
  }


  /// See AbstractAttribute::getAsStr().
  virtual const std::string getAsStr() const override {
    return getAssumed() ? "nosync" : "may-sync";
  }

  /// See AbstractAttribute::updateImpl(...).
  virtual ChangeStatus updateImpl(Attributor &A) override;

  /// Return deduced attributes in \p Attrs.
  virtual void
  getDeducedAttributes(SmallVectorImpl<Attribute> &Attrs) const override {
    LLVMContext &Ctx = AnchoredVal.getContext();
    Attrs.emplace_back(Attribute::get(Ctx, "nosync"));
  }

  /// See AbstractAttribute::getAttrKind().
  virtual Attribute::AttrKind getAttrKind() const override {
    return Attribute::None;
  }

  /// Returns true of "nosync" is assumed.
  bool isAssumedNoSync() const { return getAssumed(); }

  /// Returns true of "nosync" is known.
  bool isKnownNoSync() const { return getKnown(); }

  static constexpr Attribute::AttrKind ID =
      Attribute::AttrKind(Attribute::None - 2);

  AtomicOrdering getOrdering(Instruction *I) const;

  bool isVolatile(Instruction *I) const;
};

/// Helper function used to get ordering of an atomic instruction.
AatomicOrdering AbstractAttribute::getOrdering(Instruction *I) const {
  switch (I->getOpcode()) {
  case Instruction::AtomicRMW:
    return cast<AtomicRMWInst>(I)->getOrdering();
  case Instruction::Store:
    return cast<StoreInst>(I)->getOrdering();
  case Instruction::Load:
    return cast<LoadInst>(I)->getOrdering();
  default:
    return AtomicOrdering::NotAtomic;
  }
}

/// Helper function used to determine whether an instruction is volatile.
bool AbstractAttribute::isVolatile(Instruction *I) const {
  switch (I->getOpcode()) {
  case Instruction::AtomicRMW:
    return cast<AtomicRMWInst>(I)->isVolatile();
  case Instruction::Store:
    return cast<StoreInst>(I)->isVolatile();
  case Instruction::Load:
    return cast<LoadInst>(I)->isVolatile();
  default:
    return false;
  }
}

ChangeStatus AANoSyncFunction::updateImpl(Attributor &A) {
  Function &F = getAnchorScope();

  /// The map from instruction opcodes to those instructions in the function.
  auto &OpcodeInstMap = InfoCache.getOpcodeInstMapForFunction(F);
  auto MemoryOperators = {(unsigned)Instruction::Load,
                          (unsigned)Instruction::Store,
                          (unsigned)Instruction::AtomicRMW};

  /// We are looking for volatile instructions or Non-Relaxed atomics.
  for (auto Opcode : MemoryOperators) {
    for (Instruction *I : OpcodeInstMap[Opcode]) {
      if (!isVolatile(I) && !I->isAtomic())
        continue;

      auto ordering = getOrdering(I);

      if ((ordering == AtomicOrdering::Unordered ||
           ordering == AtomicOrdering::Monotonic) &&
          !isVolatile(I))
        continue;

      ImmutableCallSite ICS(I);
      auto *NoSyncAA = A.getAAFor<AANoSyncFunction>(*this, *I);
      if ((!NoSyncAA || !NoSyncAA->isAssumedNoSync()) &&
          !ICS.hasFnAttr("nosync") && !ICS.hasFnAttr("readnone")) {
        indicatePessimisticFixpoint();
        return ChangeStatus::CHANGED;
      }
    }
  }
  indicateOptimisticFixpoint();
  return ChangeStatus::UNCHANGED;
}

/// ----------------------------------------------------------------------------
///                               Attributor
/// ----------------------------------------------------------------------------

ChangeStatus Attributor::run() {
  // Initialize all abstract attributes.
  for (AbstractAttribute *AA : AllAbstractAttributes)
    AA->initialize(*this);

  LLVM_DEBUG(dbgs() << "[Attributor] Identified and initialized "
                    << AllAbstractAttributes.size()
                    << " abstract attributes.\n");

  // Now that all abstract attributes are collected and initialized we start the
  // abstract analysis.

  unsigned IterationCounter = 1;

  SmallVector<AbstractAttribute *, 64> ChangedAAs;
  SetVector<AbstractAttribute *> Worklist;
  Worklist.insert(AllAbstractAttributes.begin(), AllAbstractAttributes.end());

  do {
    LLVM_DEBUG(dbgs() << "\n\n[Attributor] #Iteration: " << IterationCounter
                      << ", Worklist size: " << Worklist.size() << "\n");

    // Add all abstract attributes that are potentially dependent on one that
    // changed to the work list.
    for (AbstractAttribute *ChangedAA : ChangedAAs) {
      auto &QuerriedAAs = QueryMap[ChangedAA];
      Worklist.insert(QuerriedAAs.begin(), QuerriedAAs.end());
    }

    // Reset the changed set.
    ChangedAAs.clear();

    // Update all abstract attribute in the work list and record the ones that
    // changed.
    for (AbstractAttribute *AA : Worklist)
      if (AA->update(*this) == ChangeStatus::CHANGED)
        ChangedAAs.push_back(AA);

    // Reset the work list and repopulate with the changed abstract attributes.
    // Note that dependent ones are added above.
    Worklist.clear();
    Worklist.insert(ChangedAAs.begin(), ChangedAAs.end());

  } while (!Worklist.empty() && ++IterationCounter < MaxFixpointIterations);

  LLVM_DEBUG(dbgs() << "\n[Attributor] Fixpoint iteration done after: "
                    << IterationCounter << "/" << MaxFixpointIterations
                    << " iterations\n");

  // Reset abstract arguments not settled in a sound fixpoint by now. This
  // happens when we stopped the fixpoint iteration early. Note that only the
  // ones marked as "changed" *and* the ones transitively depending on them
  // need to be reverted to a pessimistic state. Others might not be in a
  // fixpoint state but we can use the optimistic results for them anyway.
  SmallPtrSet<AbstractAttribute *, 32> Visited;
  for (unsigned u = 0; u < ChangedAAs.size(); u++) {
    AbstractAttribute *ChangedAA = ChangedAAs[u];
    if (!Visited.insert(ChangedAA).second)
      continue;

    AbstractState &State = ChangedAA->getState();
    if (!State.isAtFixpoint()) {
      State.indicatePessimisticFixpoint();

      // Bookkeeping.
      NumAttributesTimedOut++;
    }

    auto &QuerriedAAs = QueryMap[ChangedAA];
    ChangedAAs.append(QuerriedAAs.begin(), QuerriedAAs.end());
  }

  LLVM_DEBUG({
    if (!Visited.empty())
      dbgs() << "\n[Attributor] Finalized " << Visited.size()
             << " abstract attributes.\n";
  });

  unsigned NumManifested = 0;
  unsigned NumAtFixpoint = 0;
  ChangeStatus ManifestChange = ChangeStatus::UNCHANGED;
  for (AbstractAttribute *AA : AllAbstractAttributes) {
    AbstractState &State = AA->getState();

    // If there is not already a fixpoint reached we can now take the optimistic
    // state because we enforced a pessimistic one on abstract attributes we
    // needed to above.
    if (!State.isAtFixpoint())
      State.indicateOptimisticFixpoint();

    // If the state is invalid, we do not try to manifest it.
    if (!State.isValidState())
      continue;

    // Manifest the state and record if we changed the IR.
    ChangeStatus LocalChange = AA->manifest(*this);
    ManifestChange = ManifestChange | LocalChange;

    NumAtFixpoint++;
    NumManifested += (LocalChange == ChangeStatus::CHANGED);
  }

  (void)NumManifested;
  (void)NumAtFixpoint;
  LLVM_DEBUG(dbgs() << "\n[Attributor] Manifested " << NumManifested
                    << " arguments while " << NumAtFixpoint
                    << " were in a valid fixpoint state\n");

  // Bookkeeping.
  NumAttributesManifested += NumManifested;
  NumAttributesValidFixpoint += NumAtFixpoint;

  return ManifestChange;
}

void Attributor::identifyDefaultAbstractAttributes(
    Function &F, InformationCache &InfoCache,
    DenseSet</* Attribute::AttrKind */ unsigned> *Whitelist) {

    // Every function might be marked "nosync".
    registerAA(*new AANoSyncFunction(F, InfoCache));

  // Walk all instructions to find more attribute opportunities and also
  // interesting instructions that might be queried by abstract attributes
  // during their initialization or update.
  auto &ReadOrWriteInsts = InfoCache.FuncRWInstsMap[&F];
  auto &InstOpcodeMap = InfoCache.FuncInstOpcodeMap[&F];

  for (Instruction &I : instructions(&F)) {
    bool IsInterestingOpcode = false;

    switch (I.getOpcode()) {
    default:
      break;
    case Instruction::Load:
    case Instruction::Store:
    case Instruction::AtomicRMW:
      IsInterestingOpcode = true;
    }
    if (IsInterestingOpcode)
      InstOpcodeMap[I.getOpcode()].push_back(&I);
    if (I.mayReadOrWriteMemory())
      ReadOrWriteInsts.push_back(&I);
  }
}

/// Helpers to ease debugging through output streams and print calls.
///
///{
raw_ostream &llvm::operator<<(raw_ostream &OS, ChangeStatus S) {
  return OS << (S == ChangeStatus::CHANGED ? "changed" : "unchanged");
}

raw_ostream &llvm::operator<<(raw_ostream &OS,
                              AbstractAttribute::ManifestPosition AP) {
  switch (AP) {
  case AbstractAttribute::MP_ARGUMENT:
    return OS << "arg";
  case AbstractAttribute::MP_CALL_SITE_ARGUMENT:
    return OS << "cs_arg";
  case AbstractAttribute::MP_FUNCTION:
    return OS << "fn";
  case AbstractAttribute::MP_RETURNED:
    return OS << "fn_ret";
  }
  llvm_unreachable("Unknown attribute position!");
}

raw_ostream &llvm::operator<<(raw_ostream &OS, const AbstractState &S) {
  return OS << (!S.isValidState() ? "top" : (S.isAtFixpoint() ? "fix" : ""));
}

raw_ostream &llvm::operator<<(raw_ostream &OS, const AbstractAttribute &AA) {
  AA.print(OS);
  return OS;
}

void AbstractAttribute::print(raw_ostream &OS) const {
  OS << "[" << getManifestPosition() << "][" << getAsStr() << "]["
     << AnchoredVal.getName() << "]";
}
///}

/// ----------------------------------------------------------------------------
///                       Pass (Manager) Boilerplate
/// ----------------------------------------------------------------------------

static bool runAttributorOnSCC(SmallVectorImpl<Function *> &SCC) {
  if (DisableAttributor)
    return false;

  LLVM_DEBUG(dbgs() << "[Attributor] Run on SCC with " << SCC.size()
                    << " functions.\n");

  // Create an attributor and initially empty informatin cache that is filled
  // while we identify default attribute opportunities.
  Attributor A;
  InformationCache InfoCache;

  for (Function *F : SCC) {

    // TODO: Not all attributes require an exact definition. Find a way to
    //       enable deduction for some but not all attributes in case the
    //       definition might be changed at runtime, see also
    //       http://lists.llvm.org/pipermail/llvm-dev/2018-February/121275.html.
    // TODO: We could always determine abstract attributes and if sufficient
    //       information was found we could duplicate the functions that do not
    //       have an exact definition.
    if (!F->hasExactDefinition()) {

      // Bookkeeping.
      NumFnWithoutExactDefinition++;
      continue;
    }

    // For now we ignore naked and optnone functions.
    if (F->hasFnAttribute(Attribute::Naked) ||
        F->hasFnAttribute(Attribute::OptimizeNone))
      continue;

    // Bookkeeping.
    NumFnWithExactDefinition++;

    // Sanity check.
    assert(!F->isDeclaration() && "Expected a definition not a declaration!");

    // Populate the attributor with abstract attribute opportunities in the
    // function and te information cache with IR information.
    A.identifyDefaultAbstractAttributes(*F, InfoCache);
  }

  return A.run() == ChangeStatus::CHANGED;
}

PreservedAnalyses AttributorPass::run(LazyCallGraph::SCC &C,
                                      CGSCCAnalysisManager &, LazyCallGraph &,
                                      CGSCCUpdateResult &) {

  SmallVector<Function *, 16> SCCFunctions;
  for (LazyCallGraph::Node &N : C) {
    Function &Fn = N.getFunction();
    if (!Fn.isDeclaration())
      SCCFunctions.push_back(&Fn);
  }

  if (runAttributorOnSCC(SCCFunctions))
    return PreservedAnalyses::all();
  return PreservedAnalyses::none();
}

namespace {

struct AttributorLegacyPass : public CallGraphSCCPass {
  static char ID;

  AttributorLegacyPass() : CallGraphSCCPass(ID) {
    initializeAttributorLegacyPassPass(*PassRegistry::getPassRegistry());
  }

  bool runOnSCC(CallGraphSCC &SCC) override {
    if (skipSCC(SCC))
      return false;

    SmallVector<Function *, 16> SCCFunctions;
    for (CallGraphNode *I : SCC)
      if (Function *Fn = I->getFunction())
        if (!Fn->isDeclaration())
          SCCFunctions.push_back(Fn);

    return runAttributorOnSCC(SCCFunctions);
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesCFG();
    AU.addPreserved<CallGraphWrapperPass>();
    CallGraphSCCPass::getAnalysisUsage(AU);
  }
};

} // end anonymous namespace

Pass *llvm::createAttributorLegacyPass() { return new AttributorLegacyPass(); }

char AttributorLegacyPass::ID = 0;
INITIALIZE_PASS_BEGIN(AttributorLegacyPass, "attributor",
                      "Deduce and propagate attributes", false, false)
INITIALIZE_PASS_END(AttributorLegacyPass, "attributor",
                    "Deduce and propagate attributes", false, false)

