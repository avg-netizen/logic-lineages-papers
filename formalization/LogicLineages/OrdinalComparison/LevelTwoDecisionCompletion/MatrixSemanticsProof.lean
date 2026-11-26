module
public import LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.MatrixRowsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.MatrixProof
open PolynomialGraphCompletion WordLinearDecisionCompletion LevelTwoCounterexample
open LogicLineages.ModelsAlgebra.Forests

theorem positiveFold_meaningful (xs : List Nat) (ν : Nat → Nat) :
    Formula.meaningful
      (xs.foldr (fun i p => .conj (.atom (.nonnegative (positiveRow i))) p) .top) ν := by
  induction xs with
  | nil => simp [Formula.meaningful,Formula.tokens,CotreePresburgerUnit.Boolean.atoms]
  | cons i xs ih => simpa only [List.foldr_cons,meaningful_conjunction,
      meaningful_nonnegative,true_and,positiveRow_domain] using ih

theorem positiveFold_eval (xs : List Nat) (ν : Nat → Nat) :
    Formula.eval ν
      (xs.foldr (fun i p => .conj (.atom (.nonnegative (positiveRow i))) p) .top) ↔
      ∀ i ∈ xs, 0 < ν i := by
  induction xs with
  | nil => simp [Formula.eval]
  | cons i xs ih =>
      simpa only [List.foldr_cons,Formula.eval,Atom.eval,positiveRow_value,
        List.forall_mem_cons,ih] using
        and_congr (show (0 ≤ (ν i : Int)-1) ↔ 0 < ν i by omega) Iff.rfl

@[simp] theorem positiveFrame_meaningful (n : Nat) (ν : Nat → Nat) :
    Formula.meaningful (positiveFrame n) ν := positiveFold_meaningful (List.range n) ν

@[simp] theorem positiveFrame_eval (n : Nat) (ν : Nat → Nat) :
    Formula.eval ν (positiveFrame n) ↔ ∀ i < n, 0 < ν i := by
  simpa only [positiveFrame,List.mem_range] using positiveFold_eval (List.range n) ν

@[simp] theorem rowEquations_meaningful (rs : List Row) (ν : Nat → Nat) :
    Formula.meaningful (rowEquations rs) ν ↔ ∀ r ∈ rs, RowDomain r ν := by
  induction rs with
  | nil => simp [rowEquations,Formula.meaningful,Formula.tokens,CotreePresburgerUnit.Boolean.atoms]
  | cons r rs ih =>
      simpa only [rowEquations,List.foldr_cons,meaningful_conjunction,
        rowEquation_meaningful,List.forall_mem_cons] using and_congr Iff.rfl ih

@[simp] theorem rowEquations_eval (rs : List Row) (ν : Nat → Nat) :
    Formula.eval ν (rowEquations rs) ↔ ∀ r ∈ rs, RowValue r ν = 0 := by
  induction rs with
  | nil => simp [rowEquations,Formula.eval]
  | cons r rs ih =>
      simpa only [rowEquations,List.foldr_cons,Formula.eval,rowEquation_eval,
        List.forall_mem_cons] using and_congr Iff.rfl ih

/-- Literal global domains stay outside Boolean truth; in particular the
comparison row survives a true failed-positive disjunct. -/
theorem exactMatrixSemantics : Targets.ExactMatrixSemantics := by
  intro p ν
  simp only [matrix,meaningful_conjunction,meaningful_disjunction,
    positiveFrame_meaningful,rowEquations_meaningful,failedPositive_meaningful,
    badSign_meaningful,true_and,Formula.eval,positiveFrame_eval,rowEquations_eval,
    failedPositive_eval,badSign_eval,Pair.Matrix]
  constructor
  · rintro ⟨⟨hrows,hcmp⟩,hpositive,hzero,hbad⟩
    exact ⟨hpositive,fun r hr => ⟨hrows r hr,hzero r hr⟩,hcmp,hbad⟩
  · rintro ⟨hpositive,hrows,hcmp,hbad⟩
    exact ⟨⟨fun r hr => (hrows r hr).1,hcmp⟩,hpositive,
      fun r hr => (hrows r hr).2,hbad⟩

#print axioms positiveFold_meaningful
#print axioms positiveFold_eval
#print axioms positiveFrame_meaningful
#print axioms positiveFrame_eval
#print axioms rowEquations_meaningful
#print axioms rowEquations_eval
#print axioms exactMatrixSemantics

end LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.MatrixProof
