module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceCandidatesCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceCandidatesCoverage.PackingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceCandidatesCoverage.AdmissionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalOriginalUniformVertexPathSupportProof (ternaryValue)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem admitted (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed param typ raw gamma context : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing seed typ raw)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.context context seed param)))
    (hg : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.gamma gamma seed param)))
    (hguard : Nonempty (Derivation body Delta
      (graph1 (Continuation20261115.OriginalDecodedContextValidity.contextGuard n) (numeral 1) context)))
    (ha : Nonempty (Derivation body Delta
      (OriginalUniverseDecoderInternalAcceptance.TermAccepted H (OriginalUniverseDomainCoverage.member n)
        (OriginalGuardedHeadSourceCoverage.window n arity) typ raw gamma context))) :
    Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.admitted n H) (numeral 1) seed param)) := by
  have ht := OriginalTransparentDecoderValidatorCollapseInclusionProof.termSourceToTarget H
    (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
    typ raw gamma context ha
  apply InternalAcceptanceConjunctionProof.conjunctionAccept
    (.composition (Continuation20261115.OriginalDecodedContextValidity.contextGuard n)
      (fun _ : Fin 1 => leftOf (.projection 1)))
    (.composition (OriginalTypedDecoder.termCheck H)
      ![leftOf (.projection 0),rightOf (.projection 0),rightOf (.projection 1)]) ![seed,param]
  · exact unaryValue (Continuation20261115.OriginalDecodedContextValidity.contextGuard n)
      (leftOf (.projection 1)) (numeral 1) context ![seed,param] hguard hc
  · exact ternaryValue (OriginalTypedDecoder.termCheck H) (leftOf (.projection 0))
      (rightOf (.projection 0)) (rightOf (.projection 1)) (numeral 1) typ raw gamma ![seed,param] ht
      (unaryValue InternalUnpair.left (.projection 0) typ seed ![seed,param]
        (pairLeft seed typ raw hp) (projectionValue 0 ![seed,param]))
      (unaryValue InternalUnpair.right (.projection 0) raw seed ![seed,param]
        (pairRight seed typ raw hp) (projectionValue 0 ![seed,param])) hg

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceCandidatesCoverage.AdmissionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceCandidatesCoverage.AdmissionProof
