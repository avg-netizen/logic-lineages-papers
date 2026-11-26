module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalFuel (WorkFuelGraph Terminal DecreasedOrFailed)
open OriginalUniverseDecoderInternalFuel
open InternalPairingSumBounds (weakBound)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Every raw live nonempty guarded step either fails or internally constructs
strictly smaller original typed work weight. Arbitrary H, M and window ASTs. -/
def ActualOriginalUniverseInternalWorkDecrease : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (M contextWindow : Program 2) (alpha : Type)
      (state workCode previousFuel out c : OTerm alpha),
  Nonempty (Derivation body []
    ((StepLive state workCode ⊓
      ((equal workCode OrdinaryArithmetic.zeroTerm).not ⊓ WorkFuelGraph previousFuel workCode)).imp
      ((graph2 (OriginalUniverseDecoder.transition H M contextWindow) out state c).imp
        (DecreasedOrFailed out previousFuel))))

/-- Both literal terminal states remain fixed at arbitrary fuel and context. -/
def ActualOriginalUniverseInternalTerminalFixed : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (M contextWindow : Program 2) (alpha : Type)
      (out count terminal c : OTerm alpha),
  Nonempty (Derivation body []
    ((Terminal terminal).imp
      ((graph3 (OriginalUniverseDecoder.iterate H M contextWindow) out count terminal c).iff
        (equal out terminal))))

/-- Sufficient fuel concludes a terminal witness AND its actual guarded run. -/
def ActualOriginalUniverseInternalSufficientFuel : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (M contextWindow : Program 2) (alpha : Type)
      (workCode required count c : OTerm alpha),
  Nonempty (Derivation body []
    ((WorkFuelGraph required workCode ⊓ weakBound required count).imp
      (TerminatedWork H M contextWindow count workCode c)))

/-- Adding and removing spare fuel preserve acceptance above the SAME weight. -/
def ActualOriginalUniverseInternalFuelSaturation : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (M contextWindow : Program 2) (alpha : Type)
      (workCode required count c : OTerm alpha),
  Nonempty (Derivation body []
    ((WorkFuelGraph required workCode ⊓ weakBound required count).imp
      ((SuccessfulWork H M contextWindow count workCode c).iff
        (WorkAccepted H M contextWindow workCode c))))

/-- Both unchanged guarded checkers at their literal raw+1 singleton fuel. -/
def ActualOriginalUniverseInternalSingletonChecker : Prop :=
  (∀ (body : Positive (Fin 1)) (H : Program 1) (M contextWindow : Program 2) (alpha : Type)
      (workCode request gamma typ raw c : OTerm alpha),
    Nonempty (Derivation body []
      ((StepCons workCode request OrdinaryArithmetic.zeroTerm ⊓
        StepRequest request (numeral 0) gamma typ raw).imp
        ((WorkAccepted H M contextWindow workCode c).iff
          (programGraph (OriginalUniverseDecoder.termCheck H M contextWindow)
            (numeral 1) ![typ,raw,gamma,c]))))) ∧
  (∀ (body : Positive (Fin 1)) (H : Program 1) (M contextWindow : Program 2) (alpha : Type)
      (workCode request gamma types raw c : OTerm alpha),
    Nonempty (Derivation body []
      ((StepCons workCode request OrdinaryArithmetic.zeroTerm ⊓
        StepRequest request (numeral 1) gamma types raw).imp
        ((WorkAccepted H M contextWindow workCode c).iff
          (programGraph (OriginalUniverseDecoder.argumentsCheck H M contextWindow)
            (numeral 1) ![types,raw,gamma,c])))))

/-- All raw initial states and all fuels. Accepted guarded output implies the
SAME typed accepted output at IDENTICAL count and initial state, internally. -/
def ActualOriginalUniverseInternalSameFuelTypedAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (M contextWindow : Program 2) (alpha : Type)
      (count initial c : OTerm alpha),
  Nonempty (Derivation body []
    ((graph3 (OriginalUniverseDecoder.iterate H M contextWindow) (numeral 2) count initial c).imp
      (graph2 (OriginalTypedDecoder.iterate H) (numeral 2) count initial)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelTargets
