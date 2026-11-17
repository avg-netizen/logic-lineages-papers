module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.AdmissionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.PoolInclusionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.AtPrimaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCommonCandidatePool.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.AtPoolsProof
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

attribute [local irreducible] OriginalConcreteStructuralEdge.edge OriginalConcreteHeadSignature.signature OriginalCandidates.candidates OriginalDecodedContextValidity.contextGuard SeededPrimaryPool.pool

theorem bound (n : Nat) (arity : Fin n → Nat)
    (seed parameter typ raw context gamma types out candidate targetOut seedQ targetQ seedPool targetPool : OTerm alpha)
    (q : Request n arity body Delta seed parameter typ raw context gamma types out candidate targetOut)
    (hseedQ : Nonempty (Derivation body Delta (graph2 (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)) seedQ seed parameter)))
    (htargetQ : Nonempty (Derivation body Delta (graph2 (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)) targetQ candidate parameter)))
    (hseedPool : Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.pool (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity))) seedPool seed parameter)))
    (htargetPool : Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.pool (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity))) targetPool candidate parameter)))
    : Nonempty (Derivation body Delta (PrimaryMonotonicity.included targetOut out)) := by
  let H := OriginalConcreteHeadSignature.signature n arity
  let T := OriginalTypedDecoder.target H (OriginalDecodedContextValidity.contextGuard n)
  let Q := OriginalCandidates.candidates n arity H
  let P := SeededPrimaryPool.pool T Q
  let E := OriginalConcreteStructuralEdge.edge n arity
  obtain ⟨had,htargetAd⟩ := AdmissionProof.both n arity seed parameter typ raw context gamma types out candidate targetOut q
  have hinc := PoolInclusionProof.includedPools n arity seed parameter typ raw context gamma types out candidate targetOut seedQ targetQ seedPool targetPool q hseedQ htargetQ hseedPool htargetPool
  let d : PrimaryData T P E body Delta seed parameter out candidate targetOut seedPool targetPool :=
    { sourceAdmitted := had, targetAdmitted := htargetAd,
      sourcePoolGraph := hseedPool, targetPoolGraph := htargetPool,
      sourcePrimary := q.primary, targetPrimary := q.targetPrimary, member := q.member, pools := hinc }
  exact AtPrimaryProof.bound T P E seed parameter out candidate targetOut seedPool targetPool d

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.AtPoolsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.AtPoolsProof
