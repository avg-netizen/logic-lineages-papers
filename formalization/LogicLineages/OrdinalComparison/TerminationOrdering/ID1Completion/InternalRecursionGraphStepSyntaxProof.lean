module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalRecursionGraph
open SourceComputabilityFormulaSupportProof InternalRecursionGraphSyntaxProof InternalGraphCompositionSyntaxProof
open InternalSourceIntroductionSyntaxProof InternalTagArithmeticSyntaxProof InternalBinderTransportSyntaxProof
open InternalBetaTotalitySyntaxProof InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open InternalClosedProgramsBindingProof InternalDerivationRenamingSyntaxProof InternalBinderTransportProof

abbrev stepBody {n : Nat} {α : Type} (g : OFormula (Fin (n+3))) (a b t : OrdinaryArithmetic.Term α)
    (xs : Fin n → OrdinaryArithmetic.Term α) : Formula (α ⊕ Fin 3) :=
  let j : OrdinaryArithmetic.Term (α ⊕ Fin 3) := .var (.inr 0)
  let v : OrdinaryArithmetic.Term (α ⊕ Fin 3) := .var (.inr 1)
  let w : OrdinaryArithmetic.Term (α ⊕ Fin 3) := .var (.inr 2)
  ((ltF j (t.relabel Sum.inl) ⊓ beta (a.relabel Sum.inl) (b.relabel Sum.inl) j v) ⊓
    beta (a.relabel Sum.inl) (b.relabel Sum.inl) (suc j) w).imp
    (graph g w (Fin.cons j (Fin.cons v (fun i => (xs i).relabel Sum.inl))))

theorem stepAsBlock {n : Nat} {α : Type} (g : OFormula (Fin (n+3))) (a b t : OrdinaryArithmetic.Term α)
    (xs : Fin n → OrdinaryArithmetic.Term α) : step g a b t xs = InternalClosedPrograms.allBlock (stepBody g a b t xs) := by
  unfold step OrdinaryArithmetic.stepGraph
  rw [actualOriginalUniversalEmbedding]
  rfl

theorem initialRename {α β : Type} {n : Nat} (f : OFormula (Fin (n+1)))
    (a b : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α) (j : α → β) :
    (initial f a b xs).relabel j =
      initial f (a.relabel j) (b.relabel j) (fun i => (xs i).relabel j) := by
  rw [formulaRelabelAsSubst]
  change (arithmeticEmbedding.onFormula _).subst (fun x => emb (.var (j x))) = _
  rw [← embedSubst,initialGraphSubst]
  simp only [← termRelabelAsSubst]

theorem stepRename {α β : Type} {n : Nat} (g : OFormula (Fin (n+3)))
    (a b t : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α) (j : α → β) :
    (step g a b t xs).relabel j =
      step g (a.relabel j) (b.relabel j) (t.relabel j) (fun i => (xs i).relabel j) := by
  rw [formulaRelabelAsSubst]
  change (arithmeticEmbedding.onFormula _).subst (fun x => emb (.var (j x))) = _
  rw [← embedSubst,stepGraphSubst]
  simp only [← termRelabelAsSubst]

def stepValues {α : Type} (j v w : OrdinaryArithmetic.Term α) : Fin 3 → OrdinaryArithmetic.Term α :=
  Fin.cases j (Fin.cases v (fun _ => w))

theorem stepWitness {n : Nat} {α : Type} (g : OFormula (Fin (n+3)))
    (a b t j v w : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α) :
    (stepBody g a b t xs).subst (Sum.elim Term.var (fun i => emb (stepValues j v w i))) =
      ((ltF j t ⊓ beta a b j v) ⊓ beta a b (suc j) w).imp
        (graph g w (Fin.cons j (Fin.cons v xs))) := by
  have he : (Sum.elim Term.var (fun i => emb (stepValues j v w i))) =
      (fun x => emb (Sum.elim Term.var (stepValues j v w) x)) := by
    funext x
    cases x <;> rfl
  rw [he]
  change (((ltF _ _).subst _ ⊓ (beta _ _ _ _).subst _) ⊓ (beta _ _ _ _).subst _).imp
    ((graph g _ _).subst _) = _
  rw [orderSubst,betaSubst,betaSubst,graphSubst]
  simp only [witnessLift,sucSubst,Term.subst,Sum.elim_inr,stepValues,Fin.cases_zero,Fin.cases_succ]
  congr 1
  congr 1
  funext i
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => ?_) k) i <;>
    simp only [Fin.cons_zero,Fin.cons_succ,Term.subst,Sum.elim_inr,stepValues,
      Fin.cases_zero,Fin.cases_succ,witnessLift] <;> rfl

theorem recursionSubst {α β : Type} {n : Nat} (f : OFormula (Fin (n+1)))
    (g : OFormula (Fin (n+3))) (out t : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α)
    (ts : α → OrdinaryArithmetic.Term β) :
    (recursion f g out t xs).subst (fun x => emb (ts x)) =
      recursion f g (out.subst ts) (t.subst ts) (fun i => (xs i).subst ts) := by
  unfold recursion
  rw [graphSubst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun k => ?_) i <;> rfl

theorem successorStepInstantiate {n : Nat} {α : Type} (f : OFormula (Fin (n+1)))
    (g : OFormula (Fin (n+3))) (out t v : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α) :
    instantiate (recursion f g (.var (.inr (0 : Fin 1))) (t.relabel Sum.inl)
      (fun i => (xs i).relabel Sum.inl) ⊓
      graph g (out.relabel Sum.inl) (Fin.cons (t.relabel Sum.inl)
        (Fin.cons (.var (.inr 0)) (fun i => (xs i).relabel Sum.inl)))) (emb v) =
      recursion f g v t xs ⊓ graph g out (Fin.cons t (Fin.cons v xs)) := by
  rw [instantiate,bindEmbedding]
  change (recursion f g _ _ _).subst _ ⊓ (graph g _ _).subst _ = _
  rw [recursionSubst,graphSubst]
  simp only [liftBind,varBind]
  congr 1
  congr 1
  funext i
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => ?_) k) i <;>
    simp only [Fin.cons_zero,Fin.cons_succ,liftBind,varBind]

theorem liftTermRename {L : Language} {α β : Type} {k : Nat} (t : L.Term α) (j : α → β) :
    (t.relabel (Sum.inl : α → α ⊕ Fin k)).relabel (Sum.map j id) =
      (t.relabel j).relabel Sum.inl := by
  rw [Term.relabel_relabel,Term.relabel_relabel]
  rfl

theorem consTermRename {L : Language} {α β : Type} {n : Nat} (t : L.Term α)
    (xs : Fin n → L.Term α) (j : α → β) :
    (fun i : Fin (n+1) => Term.relabel j (Fin.cons (α := fun _ => L.Term α) t xs i)) =
      Fin.cons (α := fun _ => L.Term β) (t.relabel j) (fun i => (xs i).relabel j) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i <;> rfl

theorem conjunctionRename {α β : Type} (p q : Formula α) (j : α → β) :
    (p ⊓ q).relabel j = p.relabel j ⊓ q.relabel j := rfl

theorem successorStepRename {n : Nat} {α β : Type} (f : OFormula (Fin (n+1)))
    (g : OFormula (Fin (n+3))) (out t : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α) (j : α → β) :
    (successorStep f g out t xs).relabel j =
      successorStep f g (out.relabel j) (t.relabel j) (fun i => (xs i).relabel j) := by
  unfold successorStep
  rw [existsRename]
  apply congrArg existsOne
  rw [conjunctionRename,recursionRename,graphRename]
  simp only [consTermRename,liftTermRename,Term.relabel,Sum.map_inr,id_eq]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
