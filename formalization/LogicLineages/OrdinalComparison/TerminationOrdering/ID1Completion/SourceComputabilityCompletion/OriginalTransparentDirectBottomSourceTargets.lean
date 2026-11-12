module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseNormalizedBottomProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomSourceTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTransparentLambdaValidityInternal (TagIs)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Concrete decoder acceptance, not opaque calibrated source, excludes malformed tag-three values. -/
def ActualSourceTagBottom : Prop :=
  ∀ (H G : Program 1) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Gamma : List (Formula alpha))
    (packed parameter : OTerm alpha),
  Nonempty (Derivation body Gamma
    ((graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter ⊓
      TagIs 3 packed).imp (BottomRepresentative.bottomGraph (numeral 1) packed)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomSourceTargets
