module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification OriginalUniverseDecoderInternalFuel OriginalUniverseDecoderInternalAcceptance
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Factorization through the actual original list append graph at one unchanged outer context c. Neither
component is assumed valid, typed, nonempty or accepted. -/
def ActualOriginalUniverseInternalWorkAppend : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (M W : Program 2) (alpha : Type)
      (front suffix joined c : OTerm alpha),
  Nonempty (Derivation body []
    ((graph2 InternalApplicationValidityStackAppend.append joined front suffix).imp
      ((WorkAccepted H M W joined c).iff (WorkAccepted H M W front c ⊓ WorkAccepted H M W suffix c))))

/-- A literal request is independent of the unchanged suffix. -/
def ActualOriginalUniverseInternalWorkCons : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (M W : Program 2) (alpha : Type)
      (work request suffix singleton c : OTerm alpha),
  Nonempty (Derivation body []
    ((StepCons work request suffix ⊓ StepCons singleton request OrdinaryArithmetic.zeroTerm).imp
      ((WorkAccepted H M W work c).iff (WorkAccepted H M W singleton c ⊓ WorkAccepted H M W suffix c))))

/-- A paid original guarded-source step preserves precisely acceptance of the actual
output. This includes live-empty input, malformed requests and failure. -/
def ActualOriginalUniverseInternalAcceptedStep : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (M W : Program 2) (alpha : Type)
      (state work out c : OTerm alpha),
  Nonempty (Derivation body []
    ((StepLive state work ⊓ graph2 (OriginalUniverseDecoder.transition H M W) out state c).imp
      ((WorkAccepted H M W work c).iff (AcceptedState H M W out c))))

def ActualOriginalUniverseInternalVariableAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (M W : Program 2) (alpha : Type)
      (raw index typ gamma c : OTerm alpha),
  Nonempty (Derivation body []
    ((StepPair raw (numeral 0) index).imp
      ((TermAccepted H M W typ raw gamma c).iff
        (graph2 M (numeral 1) typ c ⊓ OriginalVariableDecoder.graph (numeral 1) typ index gamma))))

def ActualOriginalUniverseInternalLambdaAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (M W : Program 2) (alpha : Type)
      (raw payload domain child typ requestedDomain codomain gamma extended c : OTerm alpha),
  Nonempty (Derivation body []
    ((StepPair raw (numeral 1) payload ⊓
      (StepPair payload domain child ⊓
        (StepArrowFields typ requestedDomain codomain ⊓ StepCons extended domain gamma))).imp
      ((TermAccepted H M W typ raw gamma c).iff
        (graph2 M (numeral 1) typ c ⊓
          (graph2 M (numeral 1) domain c ⊓
            ((equal typ (numeral 0)).not ⊓
              (equal requestedDomain domain ⊓ TermAccepted H M W codomain child extended c)))))))

def ActualOriginalUniverseInternalApplicationAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (M W : Program 2) (alpha : Type)
      (raw payload domain fn arg typ arrow gamma c : OTerm alpha),
  Nonempty (Derivation body []
    ((StepPair raw (numeral 2) payload ⊓
      (StepBinaryPayload payload domain fn arg ⊓ StepCons arrow domain typ)).imp
      ((TermAccepted H M W typ raw gamma c).iff
        (graph2 M (numeral 1) typ c ⊓
          (TermAccepted H M W arrow fn gamma c ⊓ TermAccepted H M W domain arg gamma c)))))

def ActualOriginalUniverseInternalBottomAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (M W : Program 2) (alpha : Type)
      (raw payload typ gamma c : OTerm alpha),
  Nonempty (Derivation body []
    ((StepPair raw (numeral 3) payload).imp
      ((TermAccepted H M W typ raw gamma c).iff (graph2 M (numeral 1) typ c ⊓ equal payload typ))))

def ActualOriginalUniverseInternalOrdinaryAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (M W : Program 2) (alpha : Type)
      (raw payload head base headData result types typ gamma c : OTerm alpha),
  Nonempty (Derivation body []
    ((StepPair raw (numeral 4) payload ⊓
      (StepPair payload head base ⊓
        (programGraph H headData ![head] ⊓ StepArrowFields headData result types))).imp
      ((TermAccepted H M W typ raw gamma c).iff
        (graph2 M (numeral 1) typ c ⊓
          (graph2 W (numeral 1) head c ⊓
            ((equal headData (numeral 0)).not ⊓
              (equal result typ ⊓ ArgumentsAccepted H M W types base gamma c)))))))

/-- The SAME outer context is used for both children and head window. No equation matches the head's result to the recorded/requested type. -/
def ActualOriginalUniverseInternalNumberedAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (M W : Program 2) (alpha : Type)
      (raw payload label head recorded base extraTypes extras headData headResult baseTypes typ gamma c : OTerm alpha),
  Nonempty (Derivation body []
    ((StepPair raw (numeral 5) payload ⊓
      (StepNumberedPayload payload label head recorded base extraTypes extras ⊓
        (programGraph H headData ![head] ⊓ StepArrowFields headData headResult baseTypes))).imp
      ((TermAccepted H M W typ raw gamma c).iff
        (graph2 M (numeral 1) typ c ⊓
          (graph2 W (numeral 1) head c ⊓
            ((equal headData (numeral 0)).not ⊓
              (equal recorded typ ⊓
                (ArgumentsAccepted H M W baseTypes base gamma c ⊓ ArgumentsAccepted H M W extraTypes extras gamma c))))))))

def ActualOriginalUniverseInternalNilAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (M W : Program 2) (alpha : Type)
      (raw payload types gamma c : OTerm alpha),
  Nonempty (Derivation body []
    ((StepPair raw (numeral 6) payload).imp
      ((ArgumentsAccepted H M W types raw gamma c).iff
        (equal payload (numeral 0) ⊓ equal types (numeral 0)))))

def ActualOriginalUniverseInternalConsAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (M W : Program 2) (alpha : Type)
      (raw payload domain head tail types requestedDomain tailTypes gamma c : OTerm alpha),
  Nonempty (Derivation body []
    ((StepPair raw (numeral 7) payload ⊓
      (StepBinaryPayload payload domain head tail ⊓ StepArrowFields types requestedDomain tailTypes)).imp
      ((ArgumentsAccepted H M W types raw gamma c).iff
        ((equal types (numeral 0)).not ⊓
          (equal requestedDomain domain ⊓
            (TermAccepted H M W domain head gamma c ⊓ ArgumentsAccepted H M W tailTypes tail gamma c))))))

/-- The original mode restrictions reject all other arithmetic tags. -/
def ActualOriginalUniverseInternalRejectedTags : Prop :=
  (∀ (body : Positive (Fin 1)) (H : Program 1) (M W : Program 2) (alpha : Type)
      (raw tag payload typ gamma c : OTerm alpha),
    Nonempty (Derivation body []
      ((StepPair raw tag payload ⊓
        (equal tag (numeral 6) ⊔ (equal tag (numeral 7) ⊔ StepUnknownTag tag))).imp
        (TermAccepted H M W typ raw gamma c).not))) ∧
  (∀ (body : Positive (Fin 1)) (H : Program 1) (M W : Program 2) (alpha : Type)
      (raw tag payload types gamma c : OTerm alpha),
    Nonempty (Derivation body []
      ((StepPair raw tag payload ⊓
        ((equal tag (numeral 6)).not ⊓ (equal tag (numeral 7)).not)).imp
        (ArgumentsAccepted H M W types raw gamma c).not)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceTargets
