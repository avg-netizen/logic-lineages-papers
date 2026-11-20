module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityFormulaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityBindingProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalElimination)
open ID1Completion.InternalListInductionSyntaxProof (allBlockRename)
open ID1Completion.InternalRecursionGraphSyntaxProof (liftSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (allBlockSubst conjunctionSubst liftedEmbedding)
open ID1Completion.InternalBinderTransportSyntaxProof (termRelabelSubst termSubstVar)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt finishAt)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof (positiveRename finishAtRename)
open NumberedWindowInternalSparsePositiveTransitivityTargets
open NumberedWindowInternalSparsePositiveTransitivityFormulaProof

abbrev row {α : Type} (raw : Program 5) (least : Program 3) (ctx ty first : OTerm α) :
    Formula (α ⊕ Fin 4) :=
  composeAt raw least (ctx.relabel Sum.inl) (ty.relabel Sum.inl) (.var (.inr 0))
    (first.relabel Sum.inl) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))

theorem composeRename {α β : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source first mid second target : OTerm α) (j : α → β) :
    (composeAt raw least ctx ty source first mid second target).relabel j =
      composeAt raw least (ctx.relabel j) (ty.relabel j) (source.relabel j) (first.relabel j)
        (mid.relabel j) (second.relabel j) (target.relabel j) := by
  unfold composeAt
  change ((finishAt raw least ctx ty source first mid).relabel j ⊓
    (positiveAt raw least ctx ty mid second target).relabel j).imp
      ((supplied raw least ctx ty source target).relabel j) = _
  rw [finishAtRename,positiveRename,suppliedRename]

theorem composeSubst {α β : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source first mid second target : OTerm α) (ts : α → OTerm β) :
    (composeAt raw least ctx ty source first mid second target).subst (fun a => emb (ts a)) =
      composeAt raw least (ctx.subst ts) (ty.subst ts) (source.subst ts) (first.subst ts)
        (mid.subst ts) (second.subst ts) (target.subst ts) := by
  unfold composeAt
  rw [impSubst,conjunctionSubst,finishSubst,positiveSubst,suppliedSubst]

theorem uniformRename {α β : Type} (raw : Program 5) (least : Program 3) (ctx ty first : OTerm α) (j : α → β) :
    (uniformAt raw least ctx ty first).relabel j =
      uniformAt raw least (ctx.relabel j) (ty.relabel j) (first.relabel j) := by
  simp only [uniformAt,allBlockRename,composeRename,Term.relabel_relabel,Term.relabel] <;> rfl

theorem uniformSubst {α β : Type} (raw : Program 5) (least : Program 3)
    (ctx ty first : OTerm α) (ts : α → OTerm β) :
    (uniformAt raw least ctx ty first).subst (fun a => emb (ts a)) =
      uniformAt raw least (ctx.subst ts) (ty.subst ts) (first.subst ts) := by
  unfold uniformAt
  rw [allBlockSubst,liftedEmbedding,composeSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

private theorem witnessLift {α : Type} (u : OTerm α) (xs : Fin 4 → OTerm α) :
    (u.relabel Sum.inl).subst (Sum.elim Term.var xs) = u := by
  rw [termRelabelSubst]
  exact termSubstVar u

abbrev addrs {α : Type} (source mid second target : OTerm α) : Fin 4 → OTerm α := ![source,mid,second,target]

theorem rowWitness {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source first mid second target : OTerm α) :
    (row raw least ctx ty first).subst (Sum.elim Term.var (fun i => emb (addrs source mid second target i))) =
      composeAt raw least ctx ty source first mid second target := by
  let xs := addrs source mid second target
  have h : (Sum.elim Term.var (fun i => emb (xs i))) = (fun a => emb (Sum.elim Term.var xs a)) := by
    funext a
    cases a <;> rfl
  change (row raw least ctx ty first).subst (Sum.elim Term.var (fun i => emb (xs i))) = _
  unfold row
  rw [h,composeSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr] <;> rfl

theorem instantiateAt {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (raw : Program 5) (least : Program 3) (ctx ty source first mid second target : OTerm α)
    (all : Nonempty (Derivation body Γ (uniformAt raw least ctx ty first))) :
    Nonempty (Derivation body Γ (composeAt raw least ctx ty source first mid second target)) := by
  have use := actualFiniteUniversalElimination body α 4 Γ (row raw least ctx ty first)
    (fun i => emb (addrs source mid second target i)) all
  rw [rowWitness] at use
  exact use

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityBindingProof
