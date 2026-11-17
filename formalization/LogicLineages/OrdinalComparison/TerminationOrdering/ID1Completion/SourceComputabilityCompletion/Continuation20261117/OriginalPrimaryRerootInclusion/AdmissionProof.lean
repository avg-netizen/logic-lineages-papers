module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.RequestRenameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCommonCandidatePool.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.AdmissionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open TwoSol20261113.CalibratedPrimary.Membership
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalBetaTotalityProof (disjunctionElimination)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open PrimaryMonotonicity.InclusionProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

attribute [local irreducible] OriginalConcreteHeadSignature.signature OriginalCandidates.candidates OriginalDecodedContextValidity.contextGuard SeededPrimaryPool.pool

theorem both (n : Nat) (arity : Fin n → Nat)
    (seed parameter typ raw context gamma types out candidate targetOut : OTerm alpha)
    (q : Request n arity body Delta seed parameter typ raw context gamma types out candidate targetOut) :
    Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (numeral 1) seed parameter)) ∧
    Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (numeral 1) candidate parameter)) := by
  let H := OriginalConcreteHeadSignature.signature n arity
  let T := OriginalTypedDecoder.target H (OriginalDecodedContextValidity.contextGuard n)
  let Q := OriginalCandidates.candidates n arity H
  let P := SeededPrimaryPool.pool T Q
  let E := OriginalConcreteStructuralEdge.edge n arity
  have hc : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.context context seed parameter)) :=
    unaryValue InternalUnpair.left (.projection 1) context parameter ![seed,parameter]
      (pairLeft parameter context gamma q.parameterPair) (projectionValue 1 ![seed,parameter])
  have hg : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.gamma gamma seed parameter)) :=
    unaryValue InternalUnpair.right (.projection 1) gamma parameter ![seed,parameter]
      (pairRight parameter context gamma q.parameterPair) (projectionValue 1 ![seed,parameter])
  have had := OriginalSourceCandidatesCoverage.AdmissionProof.admitted n arity H
    seed parameter typ raw gamma context q.seedPair hc hg q.guard q.accepted
  have htargetAd := OriginalPrimaryTypedCarrierV2.Proof.primaryTypedCarrier n arity
    (OriginalConcreteStructuralEdge.structural n arity) body alpha Delta seed parameter out candidate had q.primary q.member
  exact ⟨had,htargetAd⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.AdmissionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.AdmissionProof
