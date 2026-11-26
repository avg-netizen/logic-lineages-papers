module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentInductionSyntaxTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentInductionSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalStrongInduction (lift)
open ID1Completion.InternalStrongInductionSyntaxProof (belowRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind zSubst sucSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (allBlockSubst liftedEmbedding)
open ID1Completion.InternalRecursionGraphSyntaxProof (liftSubst witnessLift)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowSubst)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (unarySubst)
open NumberedWindowInternalCoverAuxFragmentInductionSyntaxTargets

theorem forwardAtSubst {α β : Type} (P Q : Program 3) (ctx raw : OTerm α) (ts : α → OTerm β) :
    (forwardAt P Q ctx raw).subst (fun a => emb (ts a)) =
      forwardAt P Q (ctx.subst ts) (raw.subst ts) := by
  unfold forwardAt
  rw [impSubst,unarySubst,allBlockSubst,liftedEmbedding]
  simp only [forwardMatrix,forwardClause,impSubst,windowSubst,liftSubst,Term.subst,Sum.elim_inr,
    sucSubst,zSubst] <;> rfl

theorem forwardAtRename {α β : Type} (P Q : Program 3) (ctx raw : OTerm α) (j : α → β) :
    (forwardAt P Q ctx raw).relabel j = forwardAt P Q (ctx.relabel j) (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (forwardAt P Q ctx raw).subst (fun x => emb (.var (j x))) = _
  rw [forwardAtSubst,← termRelabelAsSubst,← termRelabelAsSubst]

theorem forwardMotiveAt {α : Type} (P Q : Program 3) (ctx raw : OTerm α) :
    instantiate (forwardMotive P Q ctx) (emb raw) = forwardAt P Q ctx raw := by
  unfold forwardMotive
  rw [instantiate,bindEmbedding,forwardAtSubst]
  simp only [liftBind,varBind]

theorem forwardResultWitness {α : Type} (P Q : Program 3) (ctx result raw : OTerm α) :
    (forwardMatrix P Q ctx raw).subst (Sum.elim Term.var (fun _ : Fin 1 => emb result)) =
      forwardClause P Q ctx result raw := by
  have he : (Sum.elim Term.var (fun _ : Fin 1 => emb result)) =
      (fun a => emb (Sum.elim Term.var (fun _ : Fin 1 => result) a)) := by
    funext a
    cases a <;> rfl
  rw [he]
  simp only [forwardMatrix,forwardClause,impSubst,windowSubst,witnessLift,Term.subst,Sum.elim_inr] <;> rfl

theorem forwardMotiveRename {α β : Type} (P Q : Program 3) (ctx : OTerm α) (j : α → β) :
    (forwardMotive P Q ctx).relabel (Sum.map j id) = forwardMotive P Q (ctx.relabel j) := by
  unfold forwardMotive
  rw [forwardAtRename]
  simp only [Term.relabel_relabel] <;> rfl

theorem forwardMotiveLift {α : Type} (P Q : Program 3) (ctx : OTerm α) :
    lift (forwardMotive P Q ctx) = forwardMotive P Q (ctx.relabel Sum.inl) := by
  exact forwardMotiveRename P Q ctx Sum.inl

theorem forwardBelowRename {α β : Type} (P Q : Program 3) (ctx raw : OTerm α) (j : α → β) :
    (forwardBelow P Q ctx raw).relabel j = forwardBelow P Q (ctx.relabel j) (raw.relabel j) := by
  rw [forwardBelow,belowRename,forwardMotiveRename] <;> rfl

#print axioms forwardAtSubst
#print axioms forwardAtRename
#print axioms forwardMotiveAt
#print axioms forwardResultWitness
#print axioms forwardMotiveRename
#print axioms forwardMotiveLift
#print axioms forwardBelowRename

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentInductionSyntaxProof
