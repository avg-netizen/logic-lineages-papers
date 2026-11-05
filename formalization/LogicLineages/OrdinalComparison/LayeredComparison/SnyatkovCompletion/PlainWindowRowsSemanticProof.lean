module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainWindowRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NestedRowsSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteBranchRowsSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ReverseWindowProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainWindowRowsSemanticProof
open NormalForm PlainWindowRows

/-- The additional anchor domain belongs to the original shifted Phi
occurrence, including when its comparison coefficient is zero. -/
theorem actualGuardCalibration : PlainWindowRowsTargets.ActualGuardCalibration := by
  intro i j e k c ν
  constructor
  · simp only [plusGuard, Formula.eval, FiniteBranchRowsSemanticProof.guardedLe_eval,
      FiniteBranchRowsSemanticProof.phi_meaningful]
    simp only [Summand.term, Nat.one_mul, closeMatrix, Matrix.eval, atMost,
      Term.value, not_lt]
    tauto
  · simp only [minusGuard, Formula.eval, FiniteBranchRowsSemanticProof.guardedLe_eval,
      FiniteBranchRowsSemanticProof.phi_meaningful]
    simp only [Summand.term, Nat.one_mul, ReverseWindow.closeMatrix, Matrix.eval,
      atMost, Term.value, not_lt]
    tauto

theorem plus_replacement_value (j : Nat) (e k : Int) (d : Nat) (ν : Nat → Nat) :
    NestedRows.replacement j k ((d : Int) - e) ν =
      (replacementTerm (shiftTerm (.variable j) k) e d).value ν := by
  simp only [NestedRows.replacement, replacementTerm, WindowProof.shifted_value,
    Term.value]
  congr 1
  omega

/-- Natural subtraction performs the inner truncation before the outer
signed shift. The second case of NestedRows retains exactly that default. -/
theorem minus_replacement_value (j : Nat) (e k : Int) (d : Nat) (ν : Nat → Nat) :
    NestedRows.replacement j (k - (d : Int)) (-e) ν =
      (ReverseWindow.replacementTerm (shiftTerm (.variable j) k) e d).value ν := by
  simp only [NestedRows.replacement, ReverseWindow.replacementTerm,
    WindowProof.shifted_value, Term.value]
  have h : ((ν j : Int) + k).toNat - d =
      ((ν j : Int) + (k - (d : Int))).toNat := by omega
  rw [h]

theorem actualCandidateSubstitution : PlainWindowRowsTargets.ActualCandidateSubstitution := by
  intro i j e k d p ν
  constructor
  · rw [plusSubstitute, NestedRowsSemanticProof.actualNestedSubstitution i j k
      ((d : Int) - e) p ν, plus_replacement_value]
  · rw [minusSubstitute, NestedRowsSemanticProof.actualNestedSubstitution i j
      (k - (d : Int)) (-e) p ν, minus_replacement_value]

/-- Pointwise comparison uses the unchanged expanded source compiler with
the anchor's original domain retained in the body. Names may coincide here. -/
theorem actualBranchCalibration : PlainWindowRowsTargets.ActualBranchCalibration := by
  intro i j e k c p ν
  constructor
  · rw [plusCases, BoundedRowsSemanticProof.any_eval, finiteWindow, WindowProof.any_truth]
    constructor
    · rintro ⟨q, hq, hv⟩
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
      have h := (actualCandidateSubstitution i j e k d
        (.conjunction (plusGuard i j e k c) p) ν).1.mp hv
      have hg := (actualGuardCalibration i j e k c _).1.mp h.1
      refine ⟨_, List.mem_map.mpr ⟨d, hd, rfl⟩, ?_⟩
      apply (WindowProof.matrix_substitution _ _ _ _).mpr
      exact ⟨hg.1, hg.2, (NormalFormSemanticProof.actualBooleanCompilation p _).mpr h.2⟩
    · rintro ⟨q, hq, hv⟩
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
      have h := (WindowProof.matrix_substitution _ _ _ _).mp hv
      refine ⟨_, List.mem_map.mpr ⟨d, hd, rfl⟩, ?_⟩
      apply (actualCandidateSubstitution i j e k d
        (.conjunction (plusGuard i j e k c) p) ν).1.mpr
      exact ⟨(actualGuardCalibration i j e k c _).1.mpr ⟨h.1, h.2.1⟩,
        (NormalFormSemanticProof.actualBooleanCompilation p _).mp h.2.2⟩
  · rw [minusCases, BoundedRowsSemanticProof.any_eval,
      ReverseWindow.finiteCases, WindowProof.any_truth]
    constructor
    · rintro ⟨q, hq, hv⟩
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
      have h := (actualCandidateSubstitution i j e k d
        (.conjunction (minusGuard i j e k c) p) ν).2.mp hv
      have hg := (actualGuardCalibration i j e k c _).2.mp h.1
      refine ⟨_, List.mem_map.mpr ⟨d, hd, rfl⟩, ?_⟩
      apply (WindowProof.matrix_substitution _ _ _ _).mpr
      exact ⟨hg.1, hg.2, (NormalFormSemanticProof.actualBooleanCompilation p _).mpr h.2⟩
    · rintro ⟨q, hq, hv⟩
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
      have h := (WindowProof.matrix_substitution _ _ _ _).mp hv
      refine ⟨_, List.mem_map.mpr ⟨d, hd, rfl⟩, ?_⟩
      apply (actualCandidateSubstitution i j e k d
        (.conjunction (minusGuard i j e k c) p) ν).2.mpr
      exact ⟨(actualGuardCalibration i j e k c _).2.mpr ⟨h.1, h.2.1⟩,
        (NormalFormSemanticProof.actualBooleanCompilation p _).mp h.2.2⟩

theorem actualFiniteElimination : PlainWindowRowsTargets.ActualFiniteElimination := by
  intro i j hij e k c p ν
  have hi : i ∉ (shiftTerm (.variable j) k).variables := by
    simpa only [shiftTerm, Term.variables, List.mem_append, List.not_mem_nil,
      or_false, List.mem_singleton] using hij
  have hb (μ : Nat → Nat) : p.compile.eval μ ↔ p.eval μ :=
    NormalFormSemanticProof.actualBooleanCompilation p μ
  have hp :
      (finiteWindow i (shiftTerm (.variable j) k) e c
        (.conjunction (shiftDomain (.variable j) k) p.compile)).eval ν ↔
      (plusCases i j e k c p).eval ν :=
    (actualBranchCalibration i j e k c p ν).1.symm
  have hm :
      (ReverseWindow.finiteCases i (shiftTerm (.variable j) k) e c
        (.conjunction (shiftDomain (.variable j) k) p.compile)).eval ν ↔
      (minusCases i j e k c p).eval ν :=
    (actualBranchCalibration i j e k c p ν).2.symm
  constructor
  · simpa only [Matrix.eval, hb, hp] using
      (WindowProof.actualFiniteElimination i (shiftTerm (.variable j) k) e c
        (.conjunction (shiftDomain (.variable j) k) p.compile) hi ν)
  · simpa only [Matrix.eval, hb, hm] using
      (ReverseWindowProof.actualFiniteElimination i (shiftTerm (.variable j) k) e c
        (.conjunction (shiftDomain (.variable j) k) p.compile) hi ν)

theorem plusGuard_variables (i j v : Nat) (e k : Int) (c : Nat) :
    v ∈ (plusGuard i j e k c).variables ↔ v = i ∨ v = j := by
  simp only [plusGuard, Formula.variables, List.mem_append,
    FiniteBranchRowsSemanticProof.guardedLe_variables, Summand.name]
  tauto

theorem minusGuard_variables (i j v : Nat) (e k : Int) (c : Nat) :
    v ∈ (minusGuard i j e k c).variables ↔ v = i ∨ v = j := by
  simp only [minusGuard, Formula.variables, List.mem_append,
    FiniteBranchRowsSemanticProof.guardedLe_variables, Summand.name]
  tauto

theorem plusSubstitute_variables (i j : Nat) (e k : Int) (d : Nat)
    (p : Formula) (v : Nat) :
    v ∈ (plusSubstitute i j e k d p).variables ↔ v = j ∨ (v ≠ i ∧ v ∈ p.variables) :=
  NestedRowsSemanticProof.exactNestedSupport i j k ((d : Int) - e) p v

theorem minusSubstitute_variables (i j : Nat) (e k : Int) (d : Nat)
    (p : Formula) (v : Nat) :
    v ∈ (minusSubstitute i j e k d p).variables ↔ v = j ∨ (v ≠ i ∧ v ∈ p.variables) :=
  NestedRowsSemanticProof.exactNestedSupport i j (k - (d : Int)) (-e) p v

theorem exactBranchSupport : PlainWindowRowsTargets.ExactBranchSupport := by
  intro i j hij e k c p v
  have hnames : v = j → v ≠ i := by
    intro hv hvi
    exact hij (hvi.symm.trans hv)
  constructor
  · rw [plusCases, BoundedRowsSemanticProof.any_variables]
    constructor
    · rintro ⟨q, hq, hv⟩
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
      have hs := (plusSubstitute_variables i j e k d
        (.conjunction (plusGuard i j e k c) p) v).mp hv
      simp only [Formula.variables, List.mem_append, plusGuard_variables] at hs
      tauto
    · intro hv
      refine ⟨_, List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
      apply (plusSubstitute_variables i j e k 0
        (.conjunction (plusGuard i j e k c) p) v).mpr
      simp only [Formula.variables, List.mem_append, plusGuard_variables]
      tauto
  · rw [minusCases, BoundedRowsSemanticProof.any_variables]
    constructor
    · rintro ⟨q, hq, hv⟩
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
      have hs := (minusSubstitute_variables i j e k d
        (.conjunction (minusGuard i j e k c) p) v).mp hv
      simp only [Formula.variables, List.mem_append, minusGuard_variables] at hs
      tauto
    · intro hv
      refine ⟨_, List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
      apply (minusSubstitute_variables i j e k 0
        (.conjunction (minusGuard i j e k c) p) v).mpr
      simp only [Formula.variables, List.mem_append, minusGuard_variables]
      tauto

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainWindowRowsSemanticProof
