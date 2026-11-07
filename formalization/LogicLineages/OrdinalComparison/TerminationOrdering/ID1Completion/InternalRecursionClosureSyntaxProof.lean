module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalRecursionGraph
open SourceComputabilityFormulaSupportProof InternalRecursionClosure InternalRecursionGraphSyntaxProof
open InternalRecursionGraphStepSyntaxProof InternalGraphCompositionSyntaxProof InternalClosedPrograms
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalTermSubstitutionSyntaxProof
open InternalFiniteBlocksSubstitutionProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalSourceInversionSupportProof
open InternalAdditionLawsProof (impSubst)
open InternalTagArithmeticSyntaxProof (emb z suc bindTerm liftBind varBind bindEmbedding nextEmbedding nextLift)

theorem conjunctionSubst {α β : Type} (p q : Formula α) (ts : α → Term β) :
    (p ⊓ q).subst ts = p.subst ts ⊓ q.subst ts := rfl

/-- Finite binding commutes with substitution of the original free names. -/
theorem allBlockSubst {α β : Type} {k : Nat} (phi : Formula (α ⊕ Fin k)) (ts : α → Term β) :
    (allBlock phi).subst ts = allBlock (phi.subst
      (Sum.elim (fun a => (ts a).relabel Sum.inl) (fun i => .var (.inr i)))) := by
  unfold allBlock
  rw [allsSubst,bindSubst]

theorem liftedEmbedding {α β : Type} (k : Nat) (ts : α → OTerm β) :
    Sum.elim (fun a => (emb (ts a)).relabel Sum.inl)
      (fun i : Fin k => (Term.var (.inr i) : Term (β ⊕ Fin k))) =
    (fun a => emb (Sum.elim (fun x => (ts x).relabel Sum.inl)
      (fun i : Fin k => (Term.var (.inr i) : OTerm (β ⊕ Fin k))) a)) := by
  funext a
  cases a with
  | inl a => exact (onTermRelabel arithmeticEmbedding Sum.inl (ts a)).symm
  | inr i => rfl

theorem totalAtSubst {α β : Type} {n : Nat} (f : OFormula (Fin (n+1)))
    (g : OFormula (Fin (n+3))) (t : OTerm α) (xs : Fin n → OTerm α) (ts : α → OTerm β) :
    (totalAt f g t xs).subst (fun a => emb (ts a)) =
      totalAt f g (t.subst ts) (fun i => (xs i).subst ts) := by
  unfold totalAt
  rw [existsSubst,liftedEmbedding,recursionSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem uniqueAtSubst {α β : Type} {n : Nat} (f : OFormula (Fin (n+1)))
    (g : OFormula (Fin (n+3))) (t : OTerm α) (xs : Fin n → OTerm α) (ts : α → OTerm β) :
    (uniqueAt f g t xs).subst (fun a => emb (ts a)) =
      uniqueAt f g (t.subst ts) (fun i => (xs i).subst ts) := by
  unfold uniqueAt
  rw [allBlockSubst,liftedEmbedding,impSubst,conjunctionSubst,recursionSubst,recursionSubst,
    ← embedSubst,equalitySubstitution]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem totalAtRename {α β : Type} {n : Nat} (f : OFormula (Fin (n+1)))
    (g : OFormula (Fin (n+3))) (t : OTerm α) (xs : Fin n → OTerm α) (j : α → β) :
    (totalAt f g t xs).relabel j =
      totalAt f g (t.relabel j) (fun i => (xs i).relabel j) := by
  rw [formulaRelabelAsSubst]
  change (totalAt f g t xs).subst (fun x => emb (.var (j x))) = _
  rw [totalAtSubst]
  simp only [← termRelabelAsSubst]

theorem uniqueAtRename {α β : Type} {n : Nat} (f : OFormula (Fin (n+1)))
    (g : OFormula (Fin (n+3))) (t : OTerm α) (xs : Fin n → OTerm α) (j : α → β) :
    (uniqueAt f g t xs).relabel j =
      uniqueAt f g (t.relabel j) (fun i => (xs i).relabel j) := by
  rw [formulaRelabelAsSubst]
  change (uniqueAt f g t xs).subst (fun x => emb (.var (j x))) = _
  rw [uniqueAtSubst]
  simp only [← termRelabelAsSubst]

theorem totalAtInstantiate {α : Type} {n : Nat} (f : OFormula (Fin (n+1)))
    (g : OFormula (Fin (n+3))) (s : OTerm α) (xs : Fin n → OTerm α) :
    instantiate (totalAt f g (.var (.inr (0 : Fin 1)))
      (fun i => (xs i).relabel Sum.inl)) (emb s) = totalAt f g s xs := by
  rw [instantiate,bindEmbedding,totalAtSubst]
  simp only [varBind,liftBind]

theorem uniqueAtInstantiate {α : Type} {n : Nat} (f : OFormula (Fin (n+1)))
    (g : OFormula (Fin (n+3))) (s : OTerm α) (xs : Fin n → OTerm α) :
    instantiate (uniqueAt f g (.var (.inr (0 : Fin 1)))
      (fun i => (xs i).relabel Sum.inl)) (emb s) = uniqueAt f g s xs := by
  rw [instantiate,bindEmbedding,uniqueAtSubst]
  simp only [varBind,liftBind]

theorem totalAtSuccessor {α : Type} {n : Nat} (f : OFormula (Fin (n+1)))
    (g : OFormula (Fin (n+3))) (xs : Fin n → OTerm α) :
    successorInstance (totalAt f g (.var (.inr (0 : Fin 1)))
      (fun i => (xs i).relabel Sum.inl)) =
    totalAt f g (suc (.var (.inr (0 : Fin 1)))) (fun i => (xs i).relabel Sum.inl) := by
  rw [successorInstance,nextEmbedding,totalAtSubst]
  simp only [InternalTagArithmeticSyntaxProof.nextTerm,Term.subst,Sum.elim_inr,nextLift]

theorem uniqueAtSuccessor {α : Type} {n : Nat} (f : OFormula (Fin (n+1)))
    (g : OFormula (Fin (n+3))) (xs : Fin n → OTerm α) :
    successorInstance (uniqueAt f g (.var (.inr (0 : Fin 1)))
      (fun i => (xs i).relabel Sum.inl)) =
    uniqueAt f g (suc (.var (.inr (0 : Fin 1)))) (fun i => (xs i).relabel Sum.inl) := by
  rw [successorInstance,nextEmbedding,uniqueAtSubst]
  simp only [InternalTagArithmeticSyntaxProof.nextTerm,Term.subst,Sum.elim_inr,nextLift]

abbrev uniqueBody {α : Type} {n : Nat} (f : OFormula (Fin (n+1)))
    (g : OFormula (Fin (n+3))) (t : OTerm α) (xs : Fin n → OTerm α) : Formula (α ⊕ Fin 2) :=
  (recursion f g (.var (.inr 0)) (t.relabel Sum.inl) (fun i => (xs i).relabel Sum.inl) ⊓
    recursion f g (.var (.inr 1)) (t.relabel Sum.inl) (fun i => (xs i).relabel Sum.inl)).imp
    (arithmeticEmbedding.onFormula ((Term.var (.inr 0) : OTerm (α ⊕ Fin 2)).equal (.var (.inr 1))))

theorem uniqueBodyWitness {α : Type} {n : Nat} (f : OFormula (Fin (n+1)))
    (g : OFormula (Fin (n+3))) (out other t : OTerm α) (xs : Fin n → OTerm α) :
    (uniqueBody f g t xs).subst
      (Sum.elim Term.var (fun i : Fin 2 => emb (Fin.cases out (fun _ => other) i))) =
    (recursion f g out t xs ⊓ recursion f g other t xs).imp
      (arithmeticEmbedding.onFormula (out.equal other)) := by
  have he : (Sum.elim Term.var (fun i : Fin 2 => emb (Fin.cases out (fun _ => other) i))) =
      (fun x => emb (Sum.elim Term.var (Fin.cases out (fun _ => other)) x)) := by
    funext x
    cases x <;> rfl
  unfold uniqueBody
  rw [he,impSubst,conjunctionSubst,recursionSubst,recursionSubst,← embedSubst,equalitySubstitution]
  simp only [witnessLift,Term.subst,Sum.elim_inr,Fin.cases_zero]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
