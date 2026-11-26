module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderStepSpecification
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors (graph2)
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedLeastCodeRepresentative
open OriginalUniverseDecoder
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- ONE local original-head/window AST, selected before every context, Gamma,
type and raw input. Its rejected cases include malformed ORIGINAL contexts. -/
def ActualOriginalUniverseWindowSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), ∃ W : Program 2, HeadWindowCalibrated n arity W

/-- The intended M is the EXISTING contextMember member. Calibration retains
its original all-vector member source and exact encoded-request universe guard. -/
def ActualOriginalUniverseGuardCalibration : Prop :=
  (∀ (n : Nat) (member : Program 2),
    (∀ v, evaluate member v = InternalOriginalUniformParameterLeaves.memberValue n v) →
    ContextMemberCalibrated n (InternalOriginalUniformContextMembership.contextMember member)) ∧
  (∀ (M W : Program 2) (v : List.Vector Nat 2),
    evaluate (guard M W) v = guardValue (programValue2 M) (programValue2 W) (v.get 0) (v.get 1)) ∧
  (∀ (n : Nat) (arity : Fin n → Nat) (ctx : OrdinaryArithmeticQuotient.Context n)
      (request : NumberedTypedRequests.Request n),
    guardValue (contextMemberValue n) (headWindowValue n arity)
      (OriginalTypedDecoder.encodeRequest request) (Encodable.encode ctx) =
        (NumberedUniverseRequests.guard arity ctx.1.1 ctx.1.2 request).toNat)

/-- Arbitrary metadata, all raw inputs and unchanged raw+1 fuel. Failure and
completion are absorbing; terminating is not the same as accepting. -/
def ActualOriginalUniverseMachineCalibration : Prop :=
  (∀ (H : Program 1) (M W : Program 2) (v : List.Vector Nat 2),
    evaluate (transition H M W) v = transitionValue (OriginalTypedDecoder.programValue H)
      (programValue2 M) (programValue2 W) (v.get 0) (v.get 1)) ∧
  (∀ (H : Nat → Nat) (M W : Nat → Nat → Nat) (context : Nat)
      (state : OriginalTypedDecoder.State),
    transitionValue H M W (OriginalTypedDecoder.encodeState state) context =
      OriginalTypedDecoder.encodeState (stateStep H M W context state)) ∧
  (∀ (H : Program 1) (M W : Program 2) (v : List.Vector Nat 3),
    evaluate (iterate H M W) v = iterateValue (OriginalTypedDecoder.programValue H)
      (programValue2 M) (programValue2 W) (v.get 0) (v.get 1) (v.get 2)) ∧
  (∀ (H : Program 1) (M W : Program 2) (v : List.Vector Nat 4),
    evaluate (termCheck H M W) v = checkValue (OriginalTypedDecoder.programValue H)
      (programValue2 M) (programValue2 W)
      (OriginalTypedDecoder.termRequestValue (v.get 2) (v.get 0) (v.get 1)) (v.get 3) ∧
    evaluate (argumentsCheck H M W) v = checkValue (OriginalTypedDecoder.programValue H)
      (programValue2 M) (programValue2 W)
      (OriginalTypedDecoder.argumentsRequestValue (v.get 2) (v.get 0) (v.get 1)) (v.get 3)) ∧
  (∀ (H : Nat → Nat) (M W : Nat → Nat → Nat) (request context count : Nat),
    OriginalTypedDecoder.requestRaw request + 1 ≤ count →
    iterateValue H M W count (OriginalTypedDecoder.initialValue request) context = 0 ∨
      iterateValue H M W count (OriginalTypedDecoder.initialValue request) context = Nat.pair 1 0)

/-- Original universe traversal at every fuel, and SAME-fuel acceptance
inclusion into the accepted typed machine at all raw states and arbitrary guards. -/
def ActualOriginalUniverseTraversal : Prop :=
  (∀ (n : Nat) (arity : Fin n → Nat) (ctx : OrdinaryArithmeticQuotient.Context n)
      (fuel : Nat) (requests : List (NumberedTypedRequests.Request n)),
    OriginalTypedDecoder.finishedValue
      (iterateValue (OriginalTypedDecoder.headSignatureValue n arity)
        (contextMemberValue n) (headWindowValue n arity) fuel
        (OriginalTypedDecoder.encodeState ⟨1,requests.map OriginalTypedDecoder.encodeRequest⟩)
        (Encodable.encode ctx)) =
      (NumberedUniverseEvaluation.evaluate arity ctx.1.1 ctx.1.2 fuel requests).toNat) ∧
  (∀ (H : Nat → Nat) (M W : Nat → Nat → Nat) (fuel initial context : Nat),
    OriginalTypedDecoder.finishedValue (iterateValue H M W fuel initial context) = 1 →
      OriginalTypedDecoder.finishedValue (OriginalTypedDecoder.iterateValue H fuel initial) = 1)

/-- Literal equality to the ORIGINAL oldSource for EVERY raw vector, together
with accepted reconstruction at original type/codeNumber/Gamma/Context codecs.
No finite-window premise or typed/canonical-input premise is introduced. -/
def ActualOriginalUniverseSourceCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (H G : Program 1) (M W : Program 2),
    OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
    OriginalTypedDecoder.ContextGuardCalibrated n G →
    ContextMemberCalibrated n M → HeadWindowCalibrated n arity W →
  (∀ v : List.Vector Nat 2, evaluate (source H G M W) v =
      InternalOriginalUniformParameterLeaves.sourceValue n arity v) ∧
  (∀ typ raw gamma context : Nat,
    evaluate (termCheck H M W) (List.Vector.ofFn ![typ,raw,gamma,context]) = 1 ↔
      ∃ (ctx : OrdinaryArithmeticQuotient.Context n) (Gamma : List Ty)
          (tau : Ty) (code : Code (Fin n)),
        Encodable.encode ctx = context ∧ Encodable.encode Gamma = gamma ∧
          typeNumber tau = typ ∧ codeNumber code = raw ∧
            NumberedUniverseRequests.valid arity ctx.1.1 ctx.1.2 (.term Gamma tau code) = true)

/-- Independent internal guards AND full guarded steps, arbitrary programs,
raw inputs and outputs. The RHS opens original pair/request arithmetic and
uses the OLD independent typed step, never a native evaluation oracle. -/
def ActualOriginalUniverseInternalStep : Prop :=
  (∀ (M W : Program 2) (body : Positive (Fin 1)) (alpha : Type)
      (out request context : OrdinaryArithmetic.Term alpha),
    Nonempty (Derivation body []
      ((graph2 (guard M W) out request context).iff
        (OriginalUniverseDecoderStepSpecification.guardSpec M W out request context)))) ∧
  (∀ (H : Program 1) (M W : Program 2) (body : Positive (Fin 1)) (alpha : Type)
      (out input context : OrdinaryArithmetic.Term alpha),
    Nonempty (Derivation body []
      ((graph2 (transition H M W) out input context).iff
        (OriginalUniverseDecoderStepSpecification.stepSpec H M W out input context))))

/-- Internal symbolic Gamma locality, for all outputs, under literal original
request relations. The local guard does not inspect Gamma or require Gamma⊆S. -/
def ActualOriginalUniverseSymbolicLocality : Prop :=
  ∀ (M W : Program 2) (body : Positive (Fin 1)) (alpha : Type)
      (out request₁ request₂ mode gamma₁ gamma₂ typ raw context : OrdinaryArithmetic.Term alpha),
    Nonempty (Derivation body []
      ((OriginalTypedDecoderStepSpecification.StepRequest request₁ mode gamma₁ typ raw ⊓
          OriginalTypedDecoderStepSpecification.StepRequest request₂ mode gamma₂ typ raw).imp
        ((graph2 (guard M W) out request₁ context).iff
          (graph2 (guard M W) out request₂ context))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTargets
