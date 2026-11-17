module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceCandidatesCoverage.AdmissionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.PlainTargetProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem unpack (H G : Program 1) (seed candidate param typ raw gamma : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate typ raw)))
    (hg : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.gamma gamma seed param)))
    (ha : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.target H G) (numeral 1) candidate param))) :
    Nonempty (Derivation body Delta (graph3 (OriginalTypedDecoder.termCheck H) (numeral 1) typ raw gamma)) := by
  have h := InternalAcceptanceConjunctionProof.conjunctionRecover _ _ ![candidate,param] ha
  have hgamma := unaryRecover InternalUnpair.right (.projection 1) gamma param ![seed,param] hg (projectionValue 1 ![seed,param])
  apply InternalAcceptanceSupportProof.compositionRecover (OriginalTypedDecoder.termCheck H)
    ![leftOf (.projection 0),rightOf (.projection 0),rightOf (.projection 1)]
    (numeral 1) ![candidate,param] ![typ,raw,gamma] (andRight h)
  intro i
  exact Fin.cases
    (unaryValue InternalUnpair.left (.projection 0) typ candidate ![candidate,param] (pairLeft candidate typ raw hp) (projectionValue 0 ![candidate,param]))
    (Fin.cases (unaryValue InternalUnpair.right (.projection 0) raw candidate ![candidate,param] (pairRight candidate typ raw hp) (projectionValue 0 ![candidate,param]))
      (Fin.cases (unaryValue InternalUnpair.right (.projection 1) gamma param ![candidate,param] hgamma (projectionValue 1 ![candidate,param])) (fun k => Fin.elim0 k))) i

theorem filtered (n : Nat) (arity : Fin n → Nat) (B : Program 3)
    (seed parameter out candidate typ left right gamma context : OTerm alpha)
    (hsp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing seed typ left)))
    (htp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate typ right)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.context context seed parameter)))
    (hg : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.gamma gamma seed parameter)))
    (hguard : Nonempty (Derivation body Delta (graph1 (OriginalDecodedContextValidity.contextGuard n) (numeral 1) context)))
    (ha : Nonempty (Derivation body Delta
      (programGraph (OriginalUniverseDecoder.termCheck (OriginalConcreteHeadSignature.signature n arity)
        (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity))
        (numeral 1) ![typ,left,gamma,context])))
    (hout : Nonempty (Derivation body Delta
      (graph2 (SeededPrimaryPool.primary
        (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n))
        (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)) (TypedPrimaryEdge.edge B)) out seed parameter)))
    (hmem : Nonempty (Derivation body Delta
      (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) out candidate))) :
    Nonempty (Derivation body Delta
      (graph3 (OriginalTypedDecoder.termCheck (OriginalConcreteHeadSignature.signature n arity)) (numeral 1) typ right gamma)) := by
  have hs := OriginalSourceCandidatesCoverage.AdmissionProof.admitted n arity
    (OriginalConcreteHeadSignature.signature n arity) seed parameter typ left gamma context hsp hc hg hguard ha
  have ht := OriginalPrimaryTypedCarrierV2.Proof.primaryTypedCarrier n arity B body alpha Delta
    seed parameter out candidate hs hout hmem
  exact unpack (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)
    seed candidate parameter typ right gamma htp hg ht
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.PlainTargetProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.PlainTargetProof
