module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.AtPoolsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.TargetPoolProof
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
open TwoSol20261113.CalibratedPrimary.Membership
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalBetaTotalityProof (disjunctionElimination)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open PrimaryMonotonicity.InclusionProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem bound (n : Nat) (arity : Fin n → Nat)
    (seed parameter typ raw context gamma types out candidate targetOut seedQ targetQ seedPool : OTerm alpha)
    (q : Request n arity body Delta seed parameter typ raw context gamma types out candidate targetOut)
    (hseedQ : Nonempty (Derivation body Delta (graph2 (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)) seedQ seed parameter)))
    (htargetQ : Nonempty (Derivation body Delta (graph2 (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)) targetQ candidate parameter)))
    (hseedPool : Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.pool (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity))) seedPool seed parameter)))
    : Nonempty (Derivation body Delta (graph2 contains (numeral 1) targetOut seed)) := by
  apply programCases (SeededPrimaryPool.pool (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity))) (Fin.cons candidate (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta targetPool hj htargetPool
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at htargetPool
  have q' := OriginalPrimaryRerootInclusion.RequestRenameProof.rename q j Theta hj
  have hseedQ' := renameInto hseedQ j Theta hj
  rw [graph2Rename] at hseedQ'
  have htargetQ' := renameInto htargetQ j Theta hj
  rw [graph2Rename] at htargetQ'
  have hseedPool' := renameInto hseedPool j Theta hj
  rw [graph2Rename] at hseedPool'
  exact AtPoolsProof.bound n arity (seed.relabel j) (parameter.relabel j) (typ.relabel j) (raw.relabel j) (context.relabel j) (gamma.relabel j) (types.relabel j) (out.relabel j) (candidate.relabel j) (targetOut.relabel j) (seedQ.relabel j) (targetQ.relabel j) (seedPool.relabel j) targetPool q' hseedQ' htargetQ' hseedPool' htargetPool

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.TargetPoolProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.TargetPoolProof
