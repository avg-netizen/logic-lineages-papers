module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptancePushProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceUnaryLocalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceUnaryLocalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (z)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalUniverseDecoderInternalAcceptance OriginalUniverseDecoderInternalAcceptanceLeafSupportProof
open OriginalTypedDecoderInternalOrdinaryGuardProof
open OriginalTypedDecoderInternalFuelDecreaseLeafProof (choiceCases weakenProof)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem acceptedGuard (H : Program 1) (M W : Program 2) (out control x y c : OTerm alpha) (P : Formula alpha)
    (hg : Nonempty (Derivation body Gamma (guardSpec out control x y P)))
    (ha : Nonempty (Derivation body Gamma (AcceptedState H M W out c))) :
    Nonempty (Derivation body Gamma ((equal control z).not ⊓ (equal x y ⊓ P))) := by
  apply choiceCases hg
  · intro Delta inc hgood
    exact hgood
  · intro Delta inc hbad
    obtain ⟨hbot⟩ := acceptedRejectImpossible H M W out c (andRight hbad) (weakenProof ha inc)
    exact ⟨Derivation.explosion hbot⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceUnaryLocalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceUnaryLocalProof
