module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceCandidatesCoverage.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceCandidatesCoverage.PackingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalOriginalUniformVertexPathSupportProof (ternaryValue)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem packed (H : Program 1) (M W : Program 2)
    (candidate typ raw gamma context : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate typ raw)))
    (ha : Nonempty (Derivation body Delta
      (OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W typ raw gamma context))) :
    Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.packedCheck H) (numeral 1) candidate gamma)) := by
  have ht := OriginalTransparentDecoderValidatorCollapseInclusionProof.termSourceToTarget H M W typ raw gamma context ha
  exact ternaryValue (OriginalTypedDecoder.termCheck H) (leftOf (.projection 0))
    (rightOf (.projection 0)) (.projection 1) (numeral 1) typ raw gamma ![candidate,gamma] ht
    (unaryValue InternalUnpair.left (.projection 0) typ candidate ![candidate,gamma]
      (pairLeft candidate typ raw hp) (projectionValue 0 ![candidate,gamma]))
    (unaryValue InternalUnpair.right (.projection 0) raw candidate ![candidate,gamma]
      (pairRight candidate typ raw hp) (projectionValue 0 ![candidate,gamma]))
    (projectionValue 1 ![candidate,gamma])

theorem root (seed param typ raw : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing seed typ raw))) :
    Nonempty (Derivation body Delta (graph2 OriginalClassCodes.rootType typ seed param)) :=
  unaryValue InternalUnpair.left (.projection 0) typ seed ![seed,param]
    (pairLeft seed typ raw hp) (projectionValue 0 ![seed,param])

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceCandidatesCoverage.PackingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceCandidatesCoverage.PackingProof
