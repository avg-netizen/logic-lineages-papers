module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open OriginalHereditaryValidity
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Full-output calibration of the explicit unary transition at EVERY raw
state for arbitrary original binary leaves. No leaf calibration, successful
decoding, Boolean-output, context-validity or source-validity premise occurs. -/
def ActualOriginalHereditaryTransitionCalibration : Prop :=
  ∀ (oldSource oldTarget member : Program 2) (state : Nat),
  evaluate (transition oldSource oldTarget member) (List.Vector.ofFn ![state]) =
    transitionValue
      (fun value parameter => evaluate oldSource (List.Vector.ofFn ![value,parameter]))
      (fun value parameter => evaluate oldTarget (List.Vector.ofFn ![value,parameter]))
      (fun value parameter => evaluate member (List.Vector.ofFn ![value,parameter])) state

/-- Compatibility with the unchanged list codec and literal pair-coded
frames, for arbitrary native leaves and every status. Parameters travel with
their frames, including the newly extended parameter at lambda bodies. -/
def ActualOriginalHereditaryEncodedTransition : Prop :=
  ∀ (oldSource oldTarget member : Nat → Nat → Nat) (state : State),
  transitionValue oldSource oldTarget member (encodeState state) =
    encodeState (stateStep oldSource oldTarget member state)

/-- Calibration of the exposed bounded AST, not calibration to ORIGINAL
source semantics. The second conjunct uses exactly payload+1 at every raw
value/parameter. Neither recursive guard equations nor redundancy is claimed. -/
def ActualOriginalHereditaryBoundedCalibration : Prop :=
  ∀ oldSource oldTarget member : Program 2,
  let sourceValue := fun value parameter =>
    evaluate oldSource (List.Vector.ofFn ![value,parameter])
  let targetValue := fun value parameter =>
    evaluate oldTarget (List.Vector.ofFn ![value,parameter])
  let memberValue := fun value parameter =>
    evaluate member (List.Vector.ofFn ![value,parameter])
  (∀ count initial : Nat,
    evaluate (iterate oldSource oldTarget member) (List.Vector.ofFn ![count,initial]) =
      iterateValue sourceValue targetValue memberValue count initial) ∧
  (∀ value parameter : Nat,
    evaluate (validator oldSource oldTarget member) (List.Vector.ofFn ![value,parameter]) =
      validatorValue sourceValue targetValue memberValue value parameter) ∧
  (∀ v : List.Vector Nat 2,
    evaluate (validator oldSource oldTarget member) v = 0 ∨
      evaluate (validator oldSource oldTarget member) v = 1)

/-- Original constructor payload bounds on ALL raw values with the indicated
literal tags. Typed child codes and runtime parameter codes need not decrease. -/
def ActualOriginalHereditaryPayloadBounds : Prop :=
  (∀ value : Nat, tagValue value = 2 →
    functionPayloadValue value + argumentPayloadValue value + 2 ≤ payloadValue value) ∧
  (∀ value : Nat, tagValue value = 1 →
    lambdaBodyPayloadValue value + 1 ≤ payloadValue value)

/-- Every nonempty live state loses a unit of ORIGINAL term-payload work.
This includes rejection by either old leaf or membership, both application
children, the extended-Gamma lambda child, and arbitrary other raw tags. -/
def ActualOriginalHereditaryWorkDecrease : Prop :=
  ∀ (oldSource oldTarget member : Nat → Nat → Nat) (state : State),
  state.status = 1 → state.work ≠ [] →
    workWeight (stateStep oldSource oldTarget member state).work < workWeight state.work

/-- Independent INTERNAL original pairing arithmetic: the actual lambda
body fuel bp+1 fits in the literal parent payload pair 1 (pair d bp).
No native calibration or semantic-to-internal reflection is a premise. -/
def ActualOriginalLambdaPayloadChildFuelBound : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (payload middle d bp : OTerm alpha),
  Nonempty (Derivation body []
    ((lambdaPayloadWitnesses payload middle d bp).imp
      (InternalPairingSumBounds.weakBound (OrdinaryArithmetic.succTerm bp) payload)))

/-- One opening step plus the actual body count fits inside the exact
parent payload+1 fuel. The count is derived INTERNALLY at the same literal
pair graphs, never externally supplied as an iteration-success hypothesis. -/
def ActualOriginalLambdaPayloadParentFuelBound : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (payload middle d bp : OTerm alpha),
  Nonempty (Derivation body []
    ((lambdaPayloadWitnesses payload middle d bp).imp
      (InternalPairingSumBounds.weakBound
        (OrdinaryArithmetic.succTerm (OrdinaryArithmetic.succTerm bp))
        (OrdinaryArithmetic.succTerm payload))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityTargets
