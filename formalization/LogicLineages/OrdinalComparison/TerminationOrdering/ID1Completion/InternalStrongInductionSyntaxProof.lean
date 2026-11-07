module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalStrongInduction
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonSyntaxProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof
open InternalTermSubstitutionSyntaxProof InternalTermSubstitutionProof
open InternalPositiveUnfoldingSupportProof InternalDerivationRenamingSyntaxProof
open InternalSourceIntroductionSyntaxProof InternalAdditionLawsProof

theorem belowSubst {α β : Type} (theta : Formula (α ⊕ Fin 1)) (t : OTerm α)
    (ts : α → OTerm β) :
    (below theta t).subst (fun a => emb (ts a)) =
      below (theta.subst (fun a => emb (InternalLeastNumberSyntaxProof.liftTerms ts a)))
        (t.subst ts) := by
  unfold below
  rw [actualUniversalSubstitution]
  have he : Sum.elim (fun a => (emb (ts a)).relabel Sum.inl)
      (fun i : Fin 1 => .var (.inr i)) =
      (fun a => emb (InternalLeastNumberSyntaxProof.liftTerms ts a)) := by
    funext a
    cases a with
    | inl a => exact (onTermRelabel arithmeticEmbedding Sum.inl (ts a)).symm
    | inr i => rfl
  rw [he,impSubst,orderSubst]
  congr 3
  rw [termRelabelSubst,termSubstRelabel]
  rfl

theorem belowRename {α β : Type} (theta : Formula (α ⊕ Fin 1))
    (t : OTerm α) (j : α → β) :
    (below theta t).relabel j =
      below (theta.relabel (Sum.map j id)) (t.relabel j) := by
  unfold below
  rw [actualUniversalRenaming]
  have hr (p q : Formula (α ⊕ Fin 1)) :
      (p.imp q).relabel (Sum.map j id) =
        (p.relabel (Sum.map j id)).imp (q.relabel (Sum.map j id)) := rfl
  rw [hr,orderRename]
  congr 3
  rw [Term.relabel_relabel,Term.relabel_relabel]
  rfl

theorem belowElimSyntax {α : Type} (theta : Formula (α ⊕ Fin 1))
    (s t : OTerm α) :
    instantiate ((ltF (.var (.inr 0)) (t.relabel Sum.inl)).imp theta) (emb s) =
      (ltF s t).imp (instantiate theta (emb s)) := by
  rw [impInstantiate,orderInstantiate]
  simp only [varBind,liftBind]

theorem belowInstantiate {α : Type} (theta : Formula (α ⊕ Fin 1)) (t : OTerm α) :
    instantiate (below (lift theta) (.var (.inr 0))) (emb t) = below theta t := by
  rw [instantiate,bindEmbedding,belowSubst]
  have hp : (lift theta).subst
      (fun a => emb (InternalLeastNumberSyntaxProof.liftTerms (bindTerm t) a)) = theta :=
    InternalLeastNumberSyntaxProof.liftPBind theta t
  rw [hp]
  rfl

theorem belowSuccessor {α : Type} (theta : Formula (α ⊕ Fin 1)) :
    successorInstance (below (lift theta) (.var (.inr 0))) =
      below (lift theta) (suc (.var (.inr 0))) := by
  rw [successorInstance,nextEmbedding,belowSubst]
  have hp : (lift theta).subst
      (fun a => emb (InternalLeastNumberSyntaxProof.liftTerms nextTerm a)) = lift theta :=
    InternalLeastNumberSyntaxProof.liftPNext theta
  rw [hp]
  rfl

theorem freshLift {α : Type} (theta : Formula (α ⊕ Fin 1)) :
    instantiate (lift theta) (emb (.var (.inr 0))) = theta :=
  actualFreshInstantiation α theta

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionSyntaxProof
