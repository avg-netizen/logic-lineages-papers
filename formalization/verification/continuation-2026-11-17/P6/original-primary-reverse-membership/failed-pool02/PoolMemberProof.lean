module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.RequestRenameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.AtPrimaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCommonCandidatePool.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.PoolMemberProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open OriginalPrimaryRerootInclusion (Request)
open OriginalPrimaryRerootInclusion.RequestRenameProof
open TwoSol20261113.CalibratedPrimary.Membership
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalBetaTotalityProof (disjunctionElimination)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open PrimaryMonotonicity.InclusionProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

attribute [local irreducible] OriginalConcreteStructuralEdge.edge OriginalConcreteHeadSignature.signature OriginalCandidates.candidates OriginalDecodedContextValidity.contextGuard SeededPrimaryPool.pool

theorem member (n : Nat) (arity : Fin n → Nat)
    (seed parameter typ raw context gamma types out candidate targetOut seedQ targetQ seedPool targetPool probe : OTerm alpha)
    (q : Request n arity body Delta seed parameter typ raw context gamma types out candidate targetOut)
    (hseedQ : Nonempty (Derivation body Delta (graph2 (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)) seedQ seed parameter)))
    (htargetQ : Nonempty (Derivation body Delta (graph2 (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)) targetQ candidate parameter)))
    (hseedPool : Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.pool (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity))) seedPool seed parameter)))
    (htargetPool : Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.pool (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity))) targetPool candidate parameter)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) seedPool probe)))
    : Nonempty (Derivation body Delta (graph2 contains (numeral 1) targetPool probe)) := by
  have h := OriginalCommonCandidatePool.Proof.commonCandidatePool n arity body alpha Delta
    seed parameter typ raw context gamma types out candidate seedQ targetQ seedPool targetPool probe
    q.seedPair q.parameterPair q.guard q.typesGraph q.closed q.accepted q.primary q.member
    hseedQ htargetQ hseedPool htargetPool
  exact h.2.2.2.2.mpr (h.2.2.2.1.mp hm)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.PoolMemberProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.PoolMemberProof
