module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalRecursionGraph
open SourceComputabilityFormulaSupportProof InternalGraphCompositionSyntaxProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalTermSubstitutionSyntaxProof
open InternalTermSubstitutionProof InternalFiniteBlocksBindingProof InternalFiniteBlocksSubstitutionProof
open InternalTagArithmeticSyntaxProof InternalBetaTotalitySyntaxProof InternalQuotientComparisonSyntaxProof
open InternalClosedProgramsBindingProof InternalSourceInversionSupportProof

abbrev initial {n : Nat} {α : Type} (f : OFormula (Fin (n+1))) (a b : OrdinaryArithmetic.Term α)
    (xs : Fin n → OrdinaryArithmetic.Term α) : Formula α :=
  arithmeticEmbedding.onFormula (OrdinaryArithmetic.initialGraph f a b xs)
abbrev step {n : Nat} {α : Type} (g : OFormula (Fin (n+3))) (a b t : OrdinaryArithmetic.Term α)
    (xs : Fin n → OrdinaryArithmetic.Term α) : Formula α :=
  arithmeticEmbedding.onFormula (OrdinaryArithmetic.stepGraph g a b t xs)
abbrev beta {α : Type} (a b i r : OrdinaryArithmetic.Term α) : Formula α :=
  arithmeticEmbedding.onFormula (OrdinaryArithmetic.betaFormula a b i r)

theorem allsSubst {L : Language} {α β : Type} {k : Nat}
    (phi : L.BoundedFormula α k) (ts : α → L.Term β) :
    phi.alls.subst ts = (phi.subst ts).alls := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change phi.all.alls.subst ts = _
    rw [ih]
    rfl

theorem forallFinSubst {α β : Type} {k : Nat} (phi : OFormula (α ⊕ Fin k))
    (ts : α → OrdinaryArithmetic.Term β) :
    (OrdinaryArithmetic.forallFin phi).subst ts = OrdinaryArithmetic.forallFin
      (phi.subst (Sum.elim (fun a => (ts a).relabel Sum.inl) (fun i => .var (.inr i)))) := by
  unfold OrdinaryArithmetic.forallFin
  rw [allsSubst,bindSubst]

theorem liftSubst {L : Language} {α β : Type} {k : Nat} (t : L.Term α)
    (ts : α → L.Term β) :
    (t.relabel (Sum.inl : α → α ⊕ Fin k)).subst
      (Sum.elim (fun a => (ts a).relabel Sum.inl) (fun i => .var (.inr i))) =
      (t.subst ts).relabel Sum.inl := by
  rw [termRelabelSubst,termSubstRelabel]
  rfl

theorem initialGraphSubst {α β : Type} {n : Nat} (f : OFormula (Fin (n+1)))
    (a b : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α) (ts : α → OrdinaryArithmetic.Term β) :
    (OrdinaryArithmetic.initialGraph f a b xs).subst ts =
      OrdinaryArithmetic.initialGraph f (a.subst ts) (b.subst ts) (fun i => (xs i).subst ts) := by
  unfold OrdinaryArithmetic.initialGraph
  rw [forallFinSubst]
  congr 1
  change ((OrdinaryArithmetic.betaFormula _ _ _ _).subst _).imp
    ((OrdinaryArithmetic.applyGraph f _ _).subst _) = _
  simp only [originalBetaSubst,applyGraphSubst,liftSubst,zSubst,Term.subst,Sum.elim_inr]

theorem stepGraphSubst {α β : Type} {n : Nat} (g : OFormula (Fin (n+3)))
    (a b t : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α) (ts : α → OrdinaryArithmetic.Term β) :
    (OrdinaryArithmetic.stepGraph g a b t xs).subst ts =
      OrdinaryArithmetic.stepGraph g (a.subst ts) (b.subst ts) (t.subst ts)
        (fun i => (xs i).subst ts) := by
  unfold OrdinaryArithmetic.stepGraph
  rw [forallFinSubst]
  congr 1
  change (((OrdinaryArithmetic.lessFormula _ _).subst _ ⊓
    (OrdinaryArithmetic.betaFormula _ _ _ _).subst _) ⊓
    (OrdinaryArithmetic.betaFormula _ _ _ _).subst _).imp
    ((OrdinaryArithmetic.applyGraph g _ _).subst _) = _
  simp only [originalOrderSubst,originalBetaSubst,applyGraphSubst,liftSubst,sucSubst,
    Term.subst,Sum.elim_inr]
  congr 1
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> simp only [Fin.cons_zero,
    Fin.cons_succ,Term.subst,Sum.elim_inr,liftSubst]

theorem actualOriginalRecursionInstance : InternalRecursionGraphTargets.ActualOriginalRecursionInstance := by
  intro n α f g out t xs
  unfold recursion graph OrdinaryArithmetic.applyGraph OrdinaryArithmetic.recursionGraph
  rw [existsFinSubst,actualOriginalBlockEmbedding]
  congr 1
  congr 1
  change ((OrdinaryArithmetic.initialGraph f _ _ _).subst _ ⊓
    (OrdinaryArithmetic.stepGraph g _ _ _ _).subst _) ⊓
    (OrdinaryArithmetic.betaFormula _ _ _ _).subst _ = _
  rw [initialGraphSubst,stepGraphSubst,originalBetaSubst]
  simp only [Term.subst,Sum.elim_inl,Sum.elim_inr,Fin.cases_zero,Fin.cases_succ,
    Fin.cons_zero,Fin.cons_succ]
  rfl

theorem witnessLift {L : Language} {α : Type} {k : Nat} (t : L.Term α) (ts : Fin k → L.Term α) :
    (t.relabel Sum.inl).subst (Sum.elim Term.var ts) = t := by
  rw [termRelabelSubst]
  exact termSubstVar t

theorem embedWitnesses {α : Type} {k : Nat} (phi : OFormula (α ⊕ Fin k))
    (ts : Fin k → OrdinaryArithmetic.Term α) :
    (arithmeticEmbedding.onFormula phi).subst (Sum.elim Term.var (fun i => emb (ts i))) =
      arithmeticEmbedding.onFormula (phi.subst (Sum.elim Term.var ts)) := by
  rw [embedSubst]
  congr 1
  funext a
  cases a <;> rfl

theorem initialWitness {α : Type} {n : Nat} (f : OFormula (Fin (n+1)))
    (a b out : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α) :
    (arithmeticEmbedding.onFormula ((OrdinaryArithmetic.betaFormula (a.relabel Sum.inl)
      (b.relabel Sum.inl) OrdinaryArithmetic.zeroTerm (.var (.inr (0 : Fin 1)))).imp
      (OrdinaryArithmetic.applyGraph f (.var (.inr 0)) (fun i => (xs i).relabel Sum.inl)))).subst
        (Sum.elim Term.var (fun _ => emb out)) = (beta a b OrdinaryArithmetic.zeroTerm out).imp (graph f out xs) := by
  rw [embedWitnesses]
  change arithmeticEmbedding.onFormula (((OrdinaryArithmetic.betaFormula _ _ _ _).subst _).imp
    ((OrdinaryArithmetic.applyGraph f _ _).subst _)) = _
  simp only [originalBetaSubst,applyGraphSubst,witnessLift,zSubst,Term.subst,Sum.elim_inr]
  rfl

theorem matrixWitness {α : Type} {n : Nat} (f : OFormula (Fin (n+1)))
    (g : OFormula (Fin (n+3))) (a b out t : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α) :
    (arithmeticEmbedding.onFormula (InternalRecursionGraph.matrix f g out t xs)).subst
      (Sum.elim Term.var (fun i : Fin 2 => emb (Fin.cases a (fun _ => b) i))) =
      (initial f a b xs ⊓ step g a b t xs) ⊓ beta a b t out := by
  rw [embedWitnesses]
  unfold InternalRecursionGraph.matrix
  change arithmeticEmbedding.onFormula (((OrdinaryArithmetic.initialGraph f _ _ _).subst _ ⊓
    (OrdinaryArithmetic.stepGraph g _ _ _ _).subst _) ⊓
    (OrdinaryArithmetic.betaFormula _ _ _ _).subst _) = _
  rw [initialGraphSubst,stepGraphSubst,originalBetaSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr,Fin.cases_zero,Fin.cases_succ]
  rfl

theorem recursionRename {α β : Type} {n : Nat} (f : OFormula (Fin (n+1)))
    (g : OFormula (Fin (n+3))) (out t : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α) (j : α → β) :
    (recursion f g out t xs).relabel j =
      recursion f g (out.relabel j) (t.relabel j) (fun i => (xs i).relabel j) := by
  unfold recursion
  rw [graphRename]
  congr 1
  funext i
  refine Fin.cases ?_ (fun k => ?_) i <;> rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
