module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCommonCandidatePool.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCommonCandidatePool.MembershipProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateSelfCoverage.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceCandidatesCoverage.AdmissionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCommonCandidatePool.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof (refl symm)
open InternalSourceInversionSupportProof (onEquality)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open TwoSol20261113.CalibratedPrimary.Membership
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalBetaTotalityProof (disjunctionElimination)
open InternalQuotientComparisonProof (orRight)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem commonCandidatePool : Targets.InternalCommonCandidatePool := by
  intro n arity body alpha Delta seed parameter typ raw context gamma types out candidate seedQ targetQ seedPool targetPool probe
    hseed hparameter hguard htypes harrow haccept hprimary hmember hseedQ htargetQ hseedPool htargetPool
  let H := OriginalConcreteHeadSignature.signature n arity
  let T := OriginalTypedDecoder.target H (OriginalDecodedContextValidity.contextGuard n)
  let Q := OriginalCandidates.candidates n arity H
  have hc : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.context context seed parameter)) :=
    unaryValue InternalUnpair.left (.projection 1) context parameter ![seed,parameter]
      (pairLeft parameter context gamma hparameter) (projectionValue 1 ![seed,parameter])
  have hg : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.gamma gamma seed parameter)) :=
    unaryValue InternalUnpair.right (.projection 1) gamma parameter ![seed,parameter]
      (pairRight parameter context gamma hparameter) (projectionValue 1 ![seed,parameter])
  have had := OriginalSourceCandidatesCoverage.AdmissionProof.admitted n arity H seed parameter typ raw gamma context
    hseed hc hg hguard haccept
  have hself := OriginalCandidateSelfCoverage.Proof.candidateSelfCoverage n arity H body alpha Delta
    seed parameter typ raw context gamma types seedQ hseed hparameter hguard htypes harrow haccept hseedQ
  have hincluded := SeededPrimaryPool.InternalProof.internalPrimaryCarrier T Q
    (OriginalConcreteStructuralEdge.edge n arity) body alpha Delta seed parameter seedPool out had hseedPool hprimary
  have hcp := PrimaryMonotonicity.InclusionProof.eliminate out seedPool candidate hincluded hmember
  have hct := (MembershipProof.tailMembership T Q seed parameter seedPool seedQ candidate had hseedQ hseedPool hself).mp hcp
  have he := OriginalCandidateRerooting.Proof.candidateRerooting n arity body alpha Delta
    seed parameter out candidate seedQ targetQ had hprimary hmember hseedQ htargetQ
  have htargetAd := OriginalPrimaryTypedCarrierV2.Proof.primaryTypedCarrier n arity
    (OriginalConcreteStructuralEdge.structural n arity) body alpha Delta seed parameter out candidate had hprimary hmember
  have htself := headTransport contains (numeral 1) seedQ targetQ (Fin.cons candidate Fin.elim0) he hct
  have hsp := MembershipProof.tailMembership T Q seed parameter seedPool seedQ probe had hseedQ hseedPool hself
  have htp := MembershipProof.tailMembership T Q candidate parameter targetPool targetQ probe htargetAd htargetQ htargetPool htself
  refine ⟨he,hself,hct,hsp,?_⟩
  constructor
  · intro hp
    obtain ⟨heq⟩ := he
    exact headTransport contains (numeral 1) targetQ seedQ (Fin.cons probe Fin.elim0) ⟨symm heq⟩ (htp.mp hp)
  · intro hm
    exact htp.mpr (headTransport contains (numeral 1) seedQ targetQ (Fin.cons probe Fin.elim0) he hm)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCommonCandidatePool.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCommonCandidatePool.Proof
