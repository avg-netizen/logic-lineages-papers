module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedInductionSyntax
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (emb bindTerm bindEmbedding nextTerm nextEmbedding)
open InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalBinderTransportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SourceFramedDefinitions SourceFramedSyntax
variable {alpha : Type}
theorem belowInstantiate (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B bound : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
 instantiate (BelowCompletion R H M W c B bound) (emb t) =
 BelowCompletion R H M W (c.subst (bindTerm t)) (B.subst (bindTerm t)) (bound.subst (bindTerm t)) := by
 rw [instantiate,bindEmbedding,belowSubst]
theorem belowSuccessor (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B bound : OTerm (alpha ⊕ Fin 1)) :
 successorInstance (BelowCompletion R H M W c B bound) =
 BelowCompletion R H M W (c.subst nextTerm) (B.subst nextTerm) (bound.subst nextTerm) := by
 rw [successorInstance,nextEmbedding,belowSubst]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedInductionSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedInductionSyntax
