module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOwnEarlierTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverOwnEarlierSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding zSubst sucSubst varBind)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (allBlockSubst liftedEmbedding)
open ID1Completion.InternalRecursionGraphSyntaxProof (liftSubst witnessLift)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalCoverLambdaDerivedOwnTargets (lambdaOwnClause)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowSubst memberSubst)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (unarySubst)
open NumberedWindowInternalCoverOwnEarlierTargets

theorem ownAllSubst {α β : Type} (W C : Program 3) (s : Settings) (q : OTerm α) (ts : α → OTerm β) :
    (ownAll W C s q).subst (fun a => emb (ts a)) = ownAll W C s (q.subst ts) := by
  unfold ownAll
  rw [allBlockSubst,liftedEmbedding]
  simp only [ownMatrix,lambdaOwnClause,impSubst,windowSubst,unarySubst,memberSubst,
    liftSubst,Term.subst,Sum.elim_inr] <;> rfl

theorem ownAllRename {α β : Type} (W C : Program 3) (s : Settings) (q : OTerm α) (j : α → β) :
    (ownAll W C s q).relabel j = ownAll W C s (q.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (ownAll W C s q).subst (fun a => emb (.var (j a))) = _
  rw [ownAllSubst,← termRelabelAsSubst]

theorem ownMotiveAt {α : Type} (V : Program 1) (W C : Program 3) (s : Settings) (q : OTerm α) :
    instantiate (ownMotive V W C s) (emb q) = ownAt V W C s q := by
  unfold ownMotive ownAt
  rw [instantiate,bindEmbedding,impSubst,unarySubst,ownAllSubst,sucSubst,zSubst,varBind]

theorem ownWitness {α : Type} (W C : Program 3) (s : Settings) (ctx ty q out : OTerm α) :
    (ownMatrix W C s q).subst (Sum.elim Term.var (fun i => emb (![ctx,ty,out] i))) =
      lambdaOwnClause W C s ctx ty q out := by
  have he : (Sum.elim Term.var (fun i => emb (![ctx,ty,out] i))) =
      (fun a => emb (Sum.elim Term.var ![ctx,ty,out] a)) := by
    funext a
    cases a <;> rfl
  rw [he]
  simp only [ownMatrix,lambdaOwnClause,impSubst,windowSubst,unarySubst,memberSubst,
    witnessLift,Term.subst,Sum.elim_inr]
  <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverOwnEarlierSyntaxProof
