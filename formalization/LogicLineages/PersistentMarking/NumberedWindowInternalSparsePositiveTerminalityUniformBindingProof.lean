module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityScratchBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityUniformBindingProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListInductionSyntaxProof (allBlockRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (allBlockSubst liftedEmbedding conjunctionSubst)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalElimination)
open ID1Completion.InternalQuotientComparisonSyntaxProof (orderSubst)
open ID1Completion.InternalOriginalOrderSyntaxProof (orderRename)
open ID1Completion.InternalRecursionGraphSyntaxProof (liftSubst)
open ID1Completion.InternalBinderTransportSyntaxProof (termRelabelSubst termSubstVar)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb sucRelabel sucSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparsePositiveIterationSuccessorProof (loopRename)
open NumberedWindowInternalSparsePositiveIterationBindingProof (loopSubst)
open NumberedWindowInternalSparsePositiveTerminalityTargets
open NumberedWindowInternalSparsePositiveTerminalityScratchBindingProof (terminalRename terminalSubst)

abbrev row {α : Type} (raw : Program 5) (least : Program 3) (ctx ty certificate : OTerm α) :
    Formula (α ⊕ Fin 3) :=
  sufficientAt raw least (.var (.inr 2)) (.var (.inr 0))
    (ctx.relabel Sum.inl) (ty.relabel Sum.inl) (.var (.inr 1)) (certificate.relabel Sum.inl)

theorem sufficientRename {α β : Type} (raw : Program 5) (least : Program 3)
    (out fuel ctx ty current cert : OTerm α) (j : α → β) :
    (sufficientAt raw least out fuel ctx ty current cert).relabel j =
      sufficientAt raw least (out.relabel j) (fuel.relabel j) (ctx.relabel j)
        (ty.relabel j) (current.relabel j) (cert.relabel j) := by
  unfold sufficientAt
  change ((ID1Completion.InternalOriginalOrderSyntaxProof.ltF cert (suc fuel)).relabel j ⊓
    ((NumberedWindowInternalSparsePositiveFoldTargets.loopGraph raw least out fuel ctx ty current cert).relabel j)).imp
    ((terminalScratch out).relabel j) = _
  rw [orderRename,sucRelabel,loopRename,terminalRename]

theorem sufficientSubst {α β : Type} (raw : Program 5) (least : Program 3)
    (out fuel ctx ty current cert : OTerm α) (ts : α → OTerm β) :
    (sufficientAt raw least out fuel ctx ty current cert).subst (fun a => emb (ts a)) =
      sufficientAt raw least (out.subst ts) (fuel.subst ts) (ctx.subst ts)
        (ty.subst ts) (current.subst ts) (cert.subst ts) := by
  unfold sufficientAt
  rw [impSubst,conjunctionSubst,orderSubst,sucSubst,loopSubst,terminalSubst]

theorem uniformRename {α β : Type} (raw : Program 5) (least : Program 3)
    (ctx ty cert : OTerm α) (j : α → β) :
    (uniformAt raw least ctx ty cert).relabel j =
      uniformAt raw least (ctx.relabel j) (ty.relabel j) (cert.relabel j) := by
  unfold uniformAt
  rw [allBlockRename,sufficientRename]
  simp only [Term.relabel_relabel]
  rfl

theorem uniformSubst {α β : Type} (raw : Program 5) (least : Program 3)
    (ctx ty cert : OTerm α) (ts : α → OTerm β) :
    (uniformAt raw least ctx ty cert).subst (fun a => emb (ts a)) =
      uniformAt raw least (ctx.subst ts) (ty.subst ts) (cert.subst ts) := by
  unfold uniformAt
  rw [allBlockSubst,liftedEmbedding,sufficientSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

private theorem unchanged {α : Type} (t : OTerm α) (args : Fin 3 → OTerm α) :
    (t.relabel Sum.inl).subst (Sum.elim Term.var args) = t := by
  rw [termRelabelSubst]
  exact termSubstVar t

private theorem rowWitness {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty cert fuel current out : OTerm α) :
    (row raw least ctx ty cert).subst (Sum.elim Term.var
      (fun i : Fin 3 => emb ((![fuel,current,out] : Fin 3 → OTerm α) i))) =
      sufficientAt raw least out fuel ctx ty current cert := by
  let args : Fin 3 → OTerm α := ![fuel,current,out]
  have lift : (Sum.elim Term.var (fun i => emb (args i))) =
      (fun a => emb (Sum.elim Term.var args a)) := by
    funext a
    cases a <;> rfl
  change (row raw least ctx ty cert).subst (Sum.elim Term.var (fun i => emb (args i))) = _
  unfold row
  rw [lift,sufficientSubst]
  simp only [unchanged,Term.subst,Sum.elim_inr] <;> rfl

theorem atFuel {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (raw : Program 5) (least : Program 3) (ctx ty cert fuel current out : OTerm α)
    (all : Nonempty (Derivation body Γ (uniformAt raw least ctx ty cert))) :
    Nonempty (Derivation body Γ (sufficientAt raw least out fuel ctx ty current cert)) := by
  have h := actualFiniteUniversalElimination body α 3 Γ (row raw least ctx ty cert)
    (fun i => emb ((![fuel,current,out] : Fin 3 → OTerm α) i)) all
  rw [rowWitness] at h
  exact h

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityUniformBindingProof
