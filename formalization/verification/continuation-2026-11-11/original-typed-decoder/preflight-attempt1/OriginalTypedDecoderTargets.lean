module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderStepSpecification
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedLeastCodeRepresentative
open NumberedNumericDecoding OriginalTypedDecoder
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- A single local-head program is selected before runtime contexts, types,
raw codes and windows. No recursive typed decoder is selected as an oracle. -/
def ActualOriginalTypedHeadSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), ∃ H : Program 1, HeadSignatureCalibrated n arity H

/-- Exact bridge to the existing Request, in both directions, using the new
literal machine codec and the ORIGINAL Gamma/type/types/code decoders. -/
def ActualOriginalTypedRequestCodec : Prop :=
  (∀ (n : Nat) (request : NumberedTypedRequests.Request n),
    decodeRequest n (encodeRequest request) = some request) ∧
  (∀ (n value : Nat) (request : NumberedTypedRequests.Request n),
    decodeRequest n value = some request → encodeRequest request = value)

/-- The literal local expansion AND bounded worklist traversal match exactly
the previously accepted source algorithms, including children-before-suffix. -/
def ActualOriginalTypedExpansion : Prop :=
  (∀ (n : Nat) (arity : Fin n → Nat) (request : NumberedTypedRequests.Request n),
    expandValue (headSignatureValue n arity) (encodeRequest request) =
      (NumberedTypedRequests.expand arity request).map (List.map encodeRequest)) ∧
  (∀ (n : Nat) (arity : Fin n → Nat) (fuel : Nat)
      (requests : List (NumberedTypedRequests.Request n)),
    finishedValue (iterateValue (headSignatureValue n arity) fuel
      (encodeState ⟨1, requests.map encodeRequest⟩)) =
      (NumberedTypedEvaluation.evaluate arity fuel requests).toNat)

/-- Native all-vector implementation correspondence for ARBITRARY metadata H.
This is not the independent internal one-step derivation below. -/
def ActualOriginalTypedMachineCalibration : Prop :=
  (∀ (H : Program 1) (v : List.Vector Nat 1),
    evaluate (transition H) v = transitionValue (programValue H) (v.get 0)) ∧
  (∀ (H : Nat → Nat) (state : State),
    transitionValue H (encodeState state) = encodeState (stateStep H state)) ∧
  (∀ (H : Program 1) (v : List.Vector Nat 2),
    evaluate (iterate H) v = iterateValue (programValue H) (v.get 0) (v.get 1)) ∧
  (∀ v : List.Vector Nat 1, evaluate finished v = finishedValue (v.get 0)) ∧
  (∀ (H : Program 1) (v : List.Vector Nat 3),
    evaluate (termCheck H) v =
      checkValue (programValue H) (termRequestValue (v.get 2) (v.get 0) (v.get 1)) ∧
    evaluate (argumentsCheck H) v =
      checkValue (programValue H) (argumentsRequestValue (v.get 2) (v.get 0) (v.get 1)))

/-- Raw-number weight, not typed syntax size or reconstruction budget.
Every request carries raw+1; malformed inputs and arbitrary H are included.
Termination only means failure or live-empty, not unconditionally success. -/
def ActualOriginalTypedFuel : Prop :=
  (∀ (H : Nat → Nat) (request : Nat) (children : List Nat),
    expandValue H request = some children → workWeight children < requestWeight request) ∧
  (∀ (H : Nat → Nat) (state : State), state.status = 1 → state.work ≠ [] →
    workWeight (stateStep H state).work < workWeight state.work) ∧
  (∀ (H : Nat → Nat) (request count : Nat), requestRaw request + 1 ≤ count →
    iterateValue H count (initialValue request) = 0 ∨
      iterateValue H count (initialValue request) = Nat.pair 1 0)

/-- ALL raw vectors, not merely valid-code simulation. Actual dependent
source decoders determine both acceptance and rejection. The reconstruction
clauses expressly require an original codeNumber for every accepted raw input. -/
def ActualOriginalTypedDecoderCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (H : Program 1), HeadSignatureCalibrated n arity H →
  (∀ v : List.Vector Nat 3,
    evaluate (termCheck H) v = termDecoderValue n arity (v.get 0) (v.get 1) (v.get 2) ∧
    evaluate (argumentsCheck H) v = argumentsDecoderValue n arity (v.get 0) (v.get 1) (v.get 2)) ∧
  (∀ v : List.Vector Nat 2,
    evaluate (packedCheck H) v = packedDecoderValue n arity (v.get 0) (v.get 1)) ∧
  (∀ typ raw gamma : Nat,
    evaluate (termCheck H) (List.Vector.ofFn ![typ,raw,gamma]) = 1 ↔
      ∃ (Gamma : List Ty) (tau : Ty) (code : Code (Fin n)),
        Encodable.encode Gamma = gamma ∧ typeNumber tau = typ ∧ codeNumber code = raw ∧
          (decodeTerm arity Gamma tau code).isSome = true) ∧
  (∀ types raw gamma : Nat,
    evaluate (argumentsCheck H) (List.Vector.ofFn ![types,raw,gamma]) = 1 ↔
      ∃ (Gamma ts : List Ty) (code : Code (Fin n)),
        Encodable.encode Gamma = gamma ∧ typesNumber ts = types ∧ codeNumber code = raw ∧
          (decodeArguments arity Gamma ts code).isSome = true)

/-- Independent arithmetic full ONE-STEP graph, all raw states/outputs,
arbitrary H, no calibration/semantic-reflection/run-success premise. The RHS
opens original pair/list graphs and explicit arithmetic constructor dispatch. -/
def ActualOriginalTypedInternalStep : Prop :=
  ∀ (H : Program 1) (body : Positive (Fin 1)) (alpha : Type)
      (out input : OrdinaryArithmetic.Term alpha),
    Nonempty (Derivation body []
      ((graph1 (transition H) out input).iff
        (OriginalTypedDecoderStepSpecification.stepSpec H out input)))

/-- Exact all-vector equality with the ORIGINAL oldTarget, including malformed
outer contexts. Only G(left parameter) and the explicit recursive checker are
used; no finite-window, successful-decoding or canonicality premise appears. -/
def ActualOriginalTypedTargetLeafCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (H G : Program 1),
    HeadSignatureCalibrated n arity H → ContextGuardCalibrated n G →
    ∀ v : List.Vector Nat 2, evaluate (target H G) v =
      InternalOriginalUniformParameterLeaves.targetValue n arity v

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTargets
