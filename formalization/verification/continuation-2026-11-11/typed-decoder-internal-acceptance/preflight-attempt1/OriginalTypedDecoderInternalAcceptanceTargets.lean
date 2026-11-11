module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel OriginalTypedDecoderInternalAcceptance
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Factorization through the actual original list append graph. Neither
component is assumed valid, typed, nonempty or accepted. -/
def ActualOriginalTypedInternalWorkAppend : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (alpha : Type)
      (front suffix joined : OTerm alpha),
  Nonempty (Derivation body []
    ((graph2 InternalApplicationValidityStackAppend.append joined front suffix).imp
      ((WorkAccepted H joined).iff (WorkAccepted H front ⊓ WorkAccepted H suffix))))

/-- A literal request is independent of the unchanged suffix. -/
def ActualOriginalTypedInternalWorkCons : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (alpha : Type)
      (work request suffix singleton : OTerm alpha),
  Nonempty (Derivation body []
    ((StepCons work request suffix ⊓ StepCons singleton request OrdinaryArithmetic.zeroTerm).imp
      ((WorkAccepted H work).iff (WorkAccepted H singleton ⊓ WorkAccepted H suffix))))

/-- A paid original step preserves precisely acceptance of the actual
output. This includes live-empty input, malformed requests and failure. -/
def ActualOriginalTypedInternalAcceptedStep : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (alpha : Type)
      (state work out : OTerm alpha),
  Nonempty (Derivation body []
    ((StepLive state work ⊓ graph1 (OriginalTypedDecoder.transition H) out state).imp
      ((WorkAccepted H work).iff (AcceptedState H out))))

def ActualOriginalTypedInternalVariableAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (alpha : Type)
      (raw index typ gamma : OTerm alpha),
  Nonempty (Derivation body []
    ((StepPair raw (numeral 0) index).imp
      ((TermAccepted H typ raw gamma).iff
        (OriginalVariableDecoder.graph (numeral 1) typ index gamma))))

def ActualOriginalTypedInternalLambdaAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (alpha : Type)
      (raw payload domain child typ requestedDomain codomain gamma extended : OTerm alpha),
  Nonempty (Derivation body []
    ((StepPair raw (numeral 1) payload ⊓
      (StepPair payload domain child ⊓
        (StepArrowFields typ requestedDomain codomain ⊓ StepCons extended domain gamma))).imp
      ((TermAccepted H typ raw gamma).iff
        ((equal typ (numeral 0)).not ⊓
          (equal requestedDomain domain ⊓ TermAccepted H codomain child extended)))))

def ActualOriginalTypedInternalApplicationAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (alpha : Type)
      (raw payload domain fn arg typ arrow gamma : OTerm alpha),
  Nonempty (Derivation body []
    ((StepPair raw (numeral 2) payload ⊓
      (StepBinaryPayload payload domain fn arg ⊓ StepCons arrow domain typ)).imp
      ((TermAccepted H typ raw gamma).iff
        (TermAccepted H arrow fn gamma ⊓ TermAccepted H domain arg gamma))))

def ActualOriginalTypedInternalBottomAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (alpha : Type)
      (raw payload typ gamma : OTerm alpha),
  Nonempty (Derivation body []
    ((StepPair raw (numeral 3) payload).imp
      ((TermAccepted H typ raw gamma).iff (equal payload typ))))

def ActualOriginalTypedInternalOrdinaryAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (alpha : Type)
      (raw payload head base headData result types typ gamma : OTerm alpha),
  Nonempty (Derivation body []
    ((StepPair raw (numeral 4) payload ⊓
      (StepPair payload head base ⊓
        (programGraph H headData ![head] ⊓ StepArrowFields headData result types))).imp
      ((TermAccepted H typ raw gamma).iff
        ((equal headData (numeral 0)).not ⊓
          (equal result typ ⊓ ArgumentsAccepted H types base gamma)))))

/-- No equation matches the head's result to the recorded/requested type. -/
def ActualOriginalTypedInternalNumberedAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (alpha : Type)
      (raw payload label head recorded base extraTypes extras headData headResult baseTypes typ gamma : OTerm alpha),
  Nonempty (Derivation body []
    ((StepPair raw (numeral 5) payload ⊓
      (StepNumberedPayload payload label head recorded base extraTypes extras ⊓
        (programGraph H headData ![head] ⊓ StepArrowFields headData headResult baseTypes))).imp
      ((TermAccepted H typ raw gamma).iff
        ((equal headData (numeral 0)).not ⊓
          (equal recorded typ ⊓
            (ArgumentsAccepted H baseTypes base gamma ⊓ ArgumentsAccepted H extraTypes extras gamma))))))

def ActualOriginalTypedInternalNilAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (alpha : Type)
      (raw payload types gamma : OTerm alpha),
  Nonempty (Derivation body []
    ((StepPair raw (numeral 6) payload).imp
      ((ArgumentsAccepted H types raw gamma).iff
        (equal payload (numeral 0) ⊓ equal types (numeral 0)))))

def ActualOriginalTypedInternalConsAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (alpha : Type)
      (raw payload domain head tail types requestedDomain tailTypes gamma : OTerm alpha),
  Nonempty (Derivation body []
    ((StepPair raw (numeral 7) payload ⊓
      (StepBinaryPayload payload domain head tail ⊓ StepArrowFields types requestedDomain tailTypes)).imp
      ((ArgumentsAccepted H types raw gamma).iff
        ((equal types (numeral 0)).not ⊓
          (equal requestedDomain domain ⊓
            (TermAccepted H domain head gamma ⊓ ArgumentsAccepted H tailTypes tail gamma))))))

/-- The original mode restrictions reject all other arithmetic tags. -/
def ActualOriginalTypedInternalRejectedTags : Prop :=
  (∀ (body : Positive (Fin 1)) (H : Program 1) (alpha : Type)
      (raw tag payload typ gamma : OTerm alpha),
    Nonempty (Derivation body []
      ((StepPair raw tag payload ⊓
        (equal tag (numeral 6) ⊔ (equal tag (numeral 7) ⊔ StepUnknownTag tag))).imp
        (TermAccepted H typ raw gamma).not))) ∧
  (∀ (body : Positive (Fin 1)) (H : Program 1) (alpha : Type)
      (raw tag payload types gamma : OTerm alpha),
    Nonempty (Derivation body []
      ((StepPair raw tag payload ⊓
        ((equal tag (numeral 6)).not ⊓ (equal tag (numeral 7)).not)).imp
        (ArgumentsAccepted H types raw gamma).not)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceTargets
