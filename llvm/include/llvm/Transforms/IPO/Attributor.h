//===- Attributor.h --- Module-wide attribute deduction ---------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Attributor: An inter procedural (abstract) "attribute" deduction framework.
//
// The Attributor framework is an inter procedural abstract analysis (fixpoint
// iteration analysis). The goal is to allow easy deduction of new attributes as
// well as information exchange between abstract attributes in-flight.
//
// The Attributor class is the driver and the link between the various abstract
// attributes. The Attributor will iterate until a fixpoint state is reached by
// all abstract attributes in-flight, or until it will enforce a pessimistic fix
// point because an iteration limit is reached.
//
// Abstract attributes, derived from the AbstractAttribute class, actually
// describe properties of the code. They can correspond to actual LLVM-IR
// attributes, or they can be more general, ultimately unrelated to LLVM-IR
// attributes. The latter is useful when an abstract attributes provides
// information to other abstract attributes in-flight but we might not want to
// manifest the information. The Attributor allows to query in-flight abstract
// attributes through the `Attributor::getAAFor` method. If used by an abstract
// attribute P, and resulting in an abstract attribute Q, the Attributor will
// automatically capture a potential dependence from Q to P. This dependence
// will automagically cause P to be reevaluated whenever Q changes.
//
// The Attributor will only reevaluated abstract attributes that might have
// changed since the last iteration. That means that the Attribute will not
// revisit all instructions/blocks/functions in the module but only query
// an update from a subset of the abstract attributes.
//
// The update method `AbstractAttribute::updateImpl` is implemented by the
// specific "abstract attribute" subclasses. The method is invoked whenever the
// currently assumed state (see the AbstractState class) might not be valid
// anymore. This can, for example, happen if the state was dependent on another
// abstract attribute that changed. In every invocation, the update method has
// to adjust the internal state of an abstract attribute to a point that is
// justifiable by the underlying IR and the current state of abstract attributes
// in-flight. Since the IR is given and assumed to be valid, the information
// derived from it can be assumed to hold. However, information derived from
// other abstract attributes is conditional on various things. If the justifying
// state changed, the `updateImpl` has to revisit the situation and potentially
// find another justification or limit the optimistic assumes made.
//
// Change is the key in this framework. Until a state of no-change, thus a
// fixpoint, is reached, the Attributor will query the abstract attributes
// in-flight to re-evaluate their state. If the (current) state is too
// optimistic, hence it cannot be justified anymore through other abstract
// attributes or the state of the IR, the state of the abstract attribute will
// have to change. Generally, we assume abstract attribute state to be a finite
// height lattice and the update function to be monotone. However, these
// conditions are not enforced because the iteration limit will guarantee
// termination. If an optimistic fixpoint is reached, or a pessimistic fix
// point is enforced after a timeout, the abstract attributes are tasked to
// manifest their result in the IR for passes to come.
//
// Attribute manifestation is not mandatory. If desired, there is support to
// generate a single LLVM-IR attribute already in the AbstractAttribute base
// class. In the simplest case, a subclass overloads
// `AbstractAttribute::getManifestPosition()` and
// `AbstractAttribute::getAttrKind()` to return the appropriate values. The
// Attributor manifestation framework will then create and place a new attribute
// if it is allowed to do so (based on the abstract state). Other use cases can
// be achieved by overloading other abstract attribute methods.
//
//
// The "mechanics" of adding a new "abstract attribute":
// - Define a class (transitively) inheriting from AbstractAttribute and one
//   (which could be the same) that (transitively) inherits from AbstractState.
//   For the latter, consider the already available BooleanState and
//   IntegerState if they fit your need, e.g., you require only a bit-encoding.
// - Implement all pure methods. Also use overloading if the attribute is not
//   conforming with the "default" behavior which is a (set of) LLVM-IR
//   attribute(s) for an argument, call site argument, function return value, or
//   function. See the class and method descriptions for more information on the
//   two "Abstract" classes and their respective methods.
// - Register opportunities for the new abstract attribute in the
//   `Attributor::identifyAbstractAttributes` method.
// - Add sufficient tests.
// - Add a Statistics object for bookkeeping. If it is a simple (set of)
//   attribute(s) manifested through the Attributor manifestation framework, see
//   the bookkeeping function in Attributor.cpp.
// - If instructions with a certain opcode are interesting to the attribute, add
//   that opcode to the switch in `Attributor::identifyAbstractAttributes`. This
//   will make it possible to query all those instructions through the
//   `Attributor::getOpcodeInstMapForFunction` interface and eliminate the need
//   to traverse the IR repeatedly.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_IPO_ATTRIBUTOR_H
#define LLVM_TRANSFORMS_IPO_ATTRIBUTOR_H

#include "llvm/Analysis/CGSCCPassManager.h"
#include "llvm/Analysis/LazyCallGraph.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/PassManager.h"

namespace llvm {

struct AbstractAttribute;

class Function;

/// Simple enum class that forces the status to be spelled out explicitly.
///
///{
enum class ChangeStatus {
  CHANGED,
  UNCHANGED,
};

ChangeStatus operator|(ChangeStatus l, ChangeStatus r);
ChangeStatus operator&(ChangeStatus l, ChangeStatus r);
///}

/// The fixpoint analysis framework that orchestrates the attribute deduction.
///
/// The Attributor provides a general abstract analysis framework (guided
/// fixpoint iteration) as well as helper functions for the deduction of
/// (LLVM-IR) attributes. However, also other code properties can be deduced,
/// propagated, and ultimately manifested through the Attributor framework. This
/// is particularly useful if these properties interact with attributes and a
/// co-scheduled deduction allows to improve the solution. Even if not, thus if
/// attributes/properties are completely isolated, they should use the
/// Attributor framework to reduce the number of fixpoint iteration frameworks
/// in the code base. Note that the Attributor design makes sure that isolated
/// attributes are not impacted, in any way, by others derived at the same time
/// if there is no cross-reasoning performed.
///
/// The public facing interface of the Attributor is kept simple and basically
/// allows abstract attributes to do two things:
///  - Query abstract attributes in-flight. There are two reasons to do this:
///    a) The optimistic state of one abstract attribute can justify an
///       optimistic state of another, allowing to framework to end up with an
///       optimistic (=best possible) fixpoint instead of one based solely on
///       information in the IR.
///    b) This avoids reimplementing various kinds of lookups, e.g., to check
///       for existing IR attributes, in favor of a single lookups interface
///       provided by an abstract attribute subclass.
///  - Query *cached* information about the IR, e.g., all instructions with a
///    certain opcode or all instructions that might access memory.
///
/// NOTE: The mechanics of adding a new "concrete" abstract attribute are
///       described in the file comment.
struct Attributor {
  ~Attributor() { DeleteContainerPointers(AllAbstractAttributes); }

  /// Run the fixpoint analyses on the call graph SCC \p SCC.
  ///
  /// \Returns CHANGED if the IR was changed, otherwise UNCHANGED.
  ChangeStatus run(SmallVectorImpl<Function *> &SCC);

  /// Lookup an abstract attribute of type \p AAType anchored at value \p V and
  /// argument number \p ArgNo. If no attribute is found and \p V is a call base
  /// instruction, the called function is tried as a value next. Thus, the
  /// returned abstract attribute might be anchored at the callee of \p V.
  ///
  /// This method is the only (supported) way an abstract attribute can retrieve
  /// information from another abstract attribute. As an example, take an
  /// abstract attribute that determines the memory access behavior for a
  /// argument (readnone, readonly, ...). It should use `getAAFor` to get the
  /// most optimistic information for other abstract attributes in-flight, e.g.
  /// the one reasoning about the "captured" state for the argument or the one
  /// reasoning on the memory access behavior of the function as a whole.
  template <typename AAType>
  const AAType *getAAFor(AbstractAttribute &QueryingAA, const Value &V,
                         int ArgNo = -1);

  /// A map from opcodes to instructions with this opcode.
  using OpcodeInstMapTy = DenseMap<unsigned, SmallVector<Instruction *, 32>>;

  /// Return the map that relates "interesting" opcodes with all instructions
  /// with that opcode in \p F.
  OpcodeInstMapTy &getOpcodeInstMapForFunction(Function &F) {
    return FuncInstOpcodeMap[&F];
  }

  /// A vector type to hold instructions.
  using InstructionVectorTy = std::vector<Instruction *>;

  /// Return the instructions in \p F that may read or write memory.
  InstructionVectorTy &getReadOrWriteInstsForFunction(Function &F) {
    return FunctionReadOrWriteInstsMap[&F];
  }

private:
  /// Introduce a new abstract attribute into the fixpoint analysis.
  template <typename AAType> AAType &registerAA(AAType &AA, int ArgNo = -1);

  /// Determine opportunities to derive attributes in \p F and create abstract
  /// attribute objects for them.
  ///
  /// Note that abstract attribute instances are generally created even if the
  /// IR already contains the information they would deduce. The most important
  /// reason for this is the single interface, the one of the abstract attribute
  /// instance, which can be queried without the need to look at the IR in
  /// various places.
  void identifyAbstractAttributes(Function &F);

  /// The set of all abstract attributes.
  ///{
  using AAVector = SmallVector<AbstractAttribute *, 64>;
  AAVector AllAbstractAttributes;
  ///}

  /// A nested map that remembers all instructions in a function with a certain
  /// instruction opcode (Instruction::getOpcode()).
  DenseMap<Function *, OpcodeInstMapTy> FuncInstOpcodeMap;

  /// A map from functions to their instructions that may read or write memory.
  DenseMap<Function *, InstructionVectorTy> FunctionReadOrWriteInstsMap;

  /// A map from abstract attributes to the ones that queried them through calls
  /// to the getAAFor<...>(...) method.
  DenseMap<AbstractAttribute *, SmallPtrSet<AbstractAttribute *, 32>> QueryMap;

  /// A nested map to lookup abstract attributes based on the anchored value and
  /// an argument positions (or -1) on the outer level, and attribute kinds
  /// (Attribute::AttrKind) on the inner level.
  ///{
  using KindToAbstractAttributeMap = DenseMap<unsigned, AbstractAttribute *>;
  DenseMap<std::pair<const Value *, int>, KindToAbstractAttributeMap> AAMap;
  ///}
};

/// An interface to query the internal state of an abstract attribute.
///
/// The abstract state is a minimal interface that allows the Attributor to
/// communicate with the abstract attributes about their internal state without
/// enforcing or exposing implementation details, e.g., the (existence of an)
/// underlying lattice.
///
/// It is sufficient to be able to query if a state is (1) valid or invalid, (2)
/// at a fixpoint, and to indicate to the state that (3) an optimistic fixpoint
/// was reached or (4) a pessimistic fixpoint was enforced.
///
/// All methods need to be implemented by the subclass. For the common use case,
/// a single boolean state or a bit-encoded state, the BooleanState and
/// IntegerState classes are already provided. A abstract attribute can inherit
/// from them to get the abstract state interface and additional methods to
/// directly modify the state based if needed. See the class comments for help.
struct AbstractState {
  virtual ~AbstractState() {}

  /// Return if this abstract state is in a valid state. If false, no
  /// information provided should be used.
  virtual bool isValidState() const = 0;

  /// Return if this abstract state is fixed, thus does not need to be updated
  /// if information changes as it cannot change itself.
  virtual bool isAtFixpoint() const = 0;

  /// Indicate that the abstract state should converge to the optimistic state.
  ///
  /// This will usually make the optimistically assumed state the known to be
  /// true state.
  virtual void indicateOptimisticFixpoint() = 0;

  /// Indicate that the abstract state should converge to the pessimistic state.
  ///
  /// This will usually revert the optimistically assumed state to the known to
  /// be true state.
  virtual void indicatePessimisticFixpoint() = 0;
};

/// Base class for all "concrete attribute" deductions.
///
/// The abstract attribute is a minimal interface that allows the Attributor to
/// orchestrate the abstract/fixpoint analysis. The design allows to hide away
/// implementation choices made for the subclasses but also to structure their
/// implementation and simplify the use of other abstract attributes in-flight.
///
/// To allow easy creation of new attributes, most methods have default
/// implementations. The ones that do not are generally straight forward, except
/// `AbstractAttribute::updateImpl` which is the location of most reasoning
/// associated with the abstract attribute. The update is invoked by the
/// Attributor in case the situation used to justify the current optimistic
/// state might have changed. The Attributor determines this automatically
/// by monitoring the `Attributor::getAAFor` calls made by abstract attributes.
///
/// The `updateImpl` method should inspect the IR and other abstract attributes
/// in-flight to justify the best possible (=optimistic) state. The actual
/// implementation is, similar to the underlying abstract state encoding, not
/// exposed. In the most common case, the `updateImpl` will go through a list of
/// reasons why its optimistic state is valid given the current information. If
/// any combination of them holds and is sufficient to justify the current
/// optimistic state, the method shall return UNCHAGED. If not, the optimistic
/// state is adjusted to the situation and the method shall return CHANGED.
///
/// If the manifestation of the "concrete attribute" deduced by the subclass
/// differs from the "default" behavior, which is a (set of) LLVM-IR
/// attribute(s) for an argument, call site argument, function return value, or
/// function, the `AbstractAttribute::manifest` method should be overloaded.
///
/// NOTE: If the state obtained via getState() is INVALID, thus if
///       AbstractAttribute::getState().isValidState() returns false, no
///       information provided by the methods of this class should be used.
/// NOTE: The Attributor currently runs as a call graph SCC pass. Partially to
///       this *current* choice there are certain limitations to what we can do.
///       As a general rule of thumb, "concrete" abstract attributes should *for
///       now* only perform "backward" information propagation. That means
///       optimistic information obtained through abstract attributes should
///       only be used at positions that precede the origin of the information
///       with regards to the program flow. More practically, information can
///       *now* be propagated from instructions to their enclosing function, but
///       *not* from call sites to the called function. The mechanisms to allow
///       both directions will be added in the future.
/// NOTE: The mechanics of adding a new "concrete" abstract attribute are
///       described in the file comment.
struct AbstractAttribute {

  /// The positions attributes can be manifested in.
  enum ManifestPosition {
    MP_ARGUMENT,           ///< An attribute for a function argument.
    MP_CALL_SITE_ARGUMENT, ///< An attribute for a call site argument.
    MP_FUNCTION,           ///< An attribute for a function as a whole.
    MP_RETURNED,           ///< An attribute for the function return value.
  };

  /// An abstract attribute associated with \p AssociatedVal and anchored at
  /// \p AnchoredVal.
  AbstractAttribute(Value *AssociatedVal, Value &AnchoredVal)
      : AssociatedVal(AssociatedVal), AnchoredVal(AnchoredVal) {}

  /// An abstract attribute associated with and anchored at \p V.
  AbstractAttribute(Value &V) : AbstractAttribute(&V, V) {}

  /// Virtual destructor.
  virtual ~AbstractAttribute() {}

  /// Initialize the state with the information in the Attributor \p A.
  ///
  /// This function is called by the Attributor once all abstract attributes
  /// have been identified. It can and shall be used for task like:
  ///  - identify existing knowledge in the IR and use it for the "known state"
  ///  - perform any work that is not going to change over time, e.g., determine
  ///    a subset of the IR, or attributes in-flight, that have to be looked at
  ///    in the `updateImpl` method.
  virtual void initialize(Attributor &A) {}

  /// Return the internal abstract state for inspection.
  virtual const AbstractState &getState() const = 0;

  /// Return the value this abstract attribute is anchored with.
  ///
  /// The anchored value might not be the associated value if the latter is not
  /// sufficient to determine where arguments will be manifested. This is mostly
  /// the case for call site arguments as the value is not sufficient to
  /// pinpoint them. Instead, we can use the call site as an anchor.
  ///
  ///{
  Value &getAnchoredValue() { return AnchoredVal; }
  const Value &getAnchoredValue() const { return AnchoredVal; }
  ///}

  /// Return the llvm::Function surrounding the anchored value.
  ///
  ///{
  Function &getAnchorScope();
  const Function &getAnchorScope() const;
  ///}

  /// Return the value this abstract attribute is associated with.
  ///
  /// The abstract state usually represents this value.
  ///
  ///{
  virtual Value *getAssociatedValue() { return AssociatedVal; }
  virtual const Value *getAssociatedValue() const { return AssociatedVal; }
  ///}

  /// Return the position this abstract state is manifested in.
  virtual ManifestPosition getManifestPosition() const = 0;

  /// Return the kind that identifies the abstract attribute implementation.
  virtual Attribute::AttrKind getAttrKind() const = 0;

  /// Return the deduced attributes in \p Attrs.
  virtual void getDeducedAttributes(SmallVectorImpl<Attribute> &Attrs) const {
    LLVMContext &Ctx = AnchoredVal.getContext();
    Attrs.emplace_back(Attribute::get(Ctx, getAttrKind()));
  }

  /// Helper functions, for debug purposes only.
  ///{
  virtual void print(raw_ostream &OS) const;
  void dump() const { print(dbgs()); }

  /// This function should return the "summarized" assumed state as string.
  virtual const std::string getAsStr() const = 0;
  ///}

  /// Allow the Attributor access to the protected methods.
  friend struct Attributor;

protected:
  /// Hook for the Attributor to trigger an update of the internal state.
  ///
  /// If this attribute is already fixed, this method will return UNCHANGED,
  /// otherwise it delegates to `AbstractAttribute::updateImpl`.
  ///
  /// \Return CHANGED if the internal state changed, otherwise UNCHANGED.
  ChangeStatus update(Attributor &A);

  /// Hook for the Attributor to trigger the manifestation of the information
  /// represented by the abstract attribute in the LLVM-IR.
  ///
  /// \Return CHANGED if the IR was altered, otherwise UNCHANGED.
  virtual ChangeStatus manifest(Attributor &A);

  /// Return the internal abstract state for careful modification.
  virtual AbstractState &getState() = 0;

  /// The actual update/transfer function which has to be implemented by the
  /// derived classes.
  ///
  /// If it is called, the environment has changed and we have to determine if
  /// the current information is still valid or adjust it otherwise.
  ///
  /// \Return CHANGED if the internal state changed, otherwise UNCHANGED.
  virtual ChangeStatus updateImpl(Attributor &A) = 0;

  /// The value this abstract attribute is associated with.
  Value *AssociatedVal;

  /// The value this abstract attribute is anchored at.
  Value &AnchoredVal;
};

/// Forward declarations of output streams for debug purposes.
///
///{
raw_ostream &operator<<(raw_ostream &OS, const AbstractAttribute &AA);
raw_ostream &operator<<(raw_ostream &OS, ChangeStatus S);
raw_ostream &operator<<(raw_ostream &OS, AbstractAttribute::ManifestPosition);
raw_ostream &operator<<(raw_ostream &OS, const AbstractState &State);
///}

struct AttributorPass : public PassInfoMixin<AttributorPass> {
  PreservedAnalyses run(LazyCallGraph::SCC &C, CGSCCAnalysisManager &AM,
                        LazyCallGraph &CG, CGSCCUpdateResult &);
};

Pass *createAttributorLegacyPass();

/// ----------------------------------------------------------------------------
///                       Abstract Attribute Classes
/// ----------------------------------------------------------------------------

} // end namespace llvm

#endif // LLVM_TRANSFORMS_IPO_FUNCTIONATTRS_H
