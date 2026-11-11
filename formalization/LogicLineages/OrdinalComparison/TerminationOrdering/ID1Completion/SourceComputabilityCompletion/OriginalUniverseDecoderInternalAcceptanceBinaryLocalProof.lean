module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptancePushTwoProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceUnaryLocalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceGuardNumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceBinaryLocalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceBinaryLocalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification OriginalUniverseDecoderInternalFuel OriginalUniverseDecoderInternalAcceptance
open OriginalUniverseDecoderInternalFuelSingletonSupportProof
open OriginalTypedDecoderInternalOrdinaryGuardProof
open OriginalUniverseDecoderInternalAcceptancePushTwoProof OriginalUniverseDecoderInternalAcceptanceUnaryLocalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Accepted source output forces the actual typed local guard and both
original child checks at the SAME outer context. No accepted child is assumed. -/
theorem guardedPushTwoAccepted (H : Program 1) (M W : Program 2) (mode₁ mode₂ : Nat)
    (out control x y gamma₁ typ₁ raw₁ gamma₂ typ₂ raw₂ c : OTerm alpha)
    (hg : Nonempty (Derivation body Gamma
      (guardSpec out control x y
        (StepPushTwo out (numeral mode₁) gamma₁ typ₁ raw₁ (numeral mode₂) gamma₂ typ₂ raw₂ z))))
    (ha : Nonempty (Derivation body Gamma (AcceptedState H M W out c))) :
    Nonempty (Derivation body Gamma
      ((equal control z).not ⊓ (equal x y ⊓
        (programGraph (checkFor H M W mode₁) (numeral 1) ![typ₁,raw₁,gamma₁,c] ⊓
          programGraph (checkFor H M W mode₂) (numeral 1) ![typ₂,raw₂,gamma₂,c])))) := by
  have hgood := acceptedGuard H M W out control x y c _ hg ha
  have hchildren := pushTwoAccepted H M W mode₁ mode₂ out gamma₁ typ₁ raw₁ gamma₂ typ₂ raw₂ c
    (andRight (andRight hgood)) ha
  exact andIntro (andLeft hgood) (andIntro (andLeft (andRight hgood)) hchildren)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceBinaryLocalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceBinaryLocalProof
