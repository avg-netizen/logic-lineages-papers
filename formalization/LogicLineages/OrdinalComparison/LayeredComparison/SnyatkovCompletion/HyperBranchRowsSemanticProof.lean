module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperBranchRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SignedRowsSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteBranchRowsSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindowProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperBranchRowsSemanticProof
open NormalForm HyperBranchRows

/-- The two guarded rows retain the domains of both original hyper
occurrences, independently of the comparison coefficient. -/
theorem actualGuardCalibration : HyperBranchRowsTargets.ActualGuardCalibration := by
  intro i j e h k l c ν
  simp only [closeGuard, Formula.eval, FiniteBranchRowsSemanticProof.guardedLe_eval,
    FiniteBranchRowsSemanticProof.hyper_meaningful]
  simp only [Summand.term, Nat.one_mul, HyperWindow.closeMatrix, Matrix.eval,
    atMost, not_lt]
  tauto

theorem indexEquality_value (i j : Nat) (e k : Int) (ν : Nat → Nat) :
    (indexEquality i j e k).eval ν ↔ (ν i : Int) + e = (ν j : Int) + k := by
  simp only [indexEquality, Formula.eval, Atom.eval, rowValue, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Summand.term, Term.value,
    one_mul, neg_one_mul, add_zero]
  omega

/-- The original domains are essential here: equality of signed integers
matches equality of total natural index terms only on those domains. -/
theorem indexEquality_eval (i j : Nat) (e h k l : Int) (c : Nat) (ν : Nat → Nat)
    (hc : (HyperWindow.closeMatrix i j e h k l c).eval ν) :
    (indexEquality i j e k).eval ν ↔
      (HyperWindow.indexTerm i e).value ν = (HyperWindow.indexTerm j k).value ν := by
  have hi : 0 ≤ (ν i : Int) + e :=
    (FiniteBranchRowsSemanticProof.shiftDomain_eval (.variable i) e ν).mp hc.1.1
  have hj : 0 ≤ (ν j : Int) + k :=
    (FiniteBranchRowsSemanticProof.shiftDomain_eval (.variable j) k ν).mp hc.2.1.1
  rw [indexEquality_value]
  simp only [HyperWindow.indexTerm, WindowProof.shifted_value, Term.value]
  omega

theorem matrix_bounded_truth (p : Matrix) (i bound : Nat) (ν : Nat → Nat) :
    (Matrix.any ((List.range bound).map (fun n => p.substitute i (.numeral n)))).eval ν ↔
      ∃ n : Nat, n < bound ∧ p.eval (Function.update ν i n) := by
  rw [WindowProof.any_truth]
  constructor
  · rintro ⟨q, hq, hp⟩
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hq
    exact ⟨n, List.mem_range.mp hn, (WindowProof.matrix_substitution _ _ _ _).mp hp⟩
  · rintro ⟨n, hn, hp⟩
    exact ⟨_, List.mem_map.mpr ⟨n, List.mem_range.mpr hn, rfl⟩,
      (WindowProof.matrix_substitution _ _ _ _).mpr hp⟩

theorem actualBranchCalibration : HyperBranchRowsTargets.ActualBranchCalibration := by
  intro i j e h k l c p ν
  refine ⟨?_, ?_, ?_⟩
  · rw [leftCases, BoundedRowsSemanticProof.actualBoundedElimination i
      (HyperWindow.leftBound e h l) (.conjunction (closeGuard i j e h k l c) p) ν,
      HyperWindow.leftCases, matrix_bounded_truth]
    constructor
    · rintro ⟨n, hn, hg, hp⟩
      exact ⟨n, hn, (actualGuardCalibration i j e h k l c _).mp hg,
        (NormalFormSemanticProof.actualBooleanCompilation p _).mpr hp⟩
    · rintro ⟨n, hn, hg, hp⟩
      exact ⟨n, hn, (actualGuardCalibration i j e h k l c _).mpr hg,
        (NormalFormSemanticProof.actualBooleanCompilation p _).mp hp⟩
  · rw [rightCases, BoundedRowsSemanticProof.actualBoundedElimination j
      (HyperWindow.rightBound h k l c) (.conjunction (closeGuard i j e h k l c) p) ν,
      HyperWindow.rightCases, matrix_bounded_truth]
    constructor
    · rintro ⟨n, hn, hg, hp⟩
      exact ⟨n, hn, (actualGuardCalibration i j e h k l c _).mp hg,
        (NormalFormSemanticProof.actualBooleanCompilation p _).mpr hp⟩
    · rintro ⟨n, hn, hg, hp⟩
      exact ⟨n, hn, (actualGuardCalibration i j e h k l c _).mpr hg,
        (NormalFormSemanticProof.actualBooleanCompilation p _).mp hp⟩
  · rw [equalCases, SignedRowsSemanticProof.actualTotalSubstitution i j (k - e)
      (.conjunction (indexEquality i j e k) (.conjunction (closeGuard i j e h k l c) p)) ν,
      HyperWindow.equalCases, WindowProof.matrix_substitution]
    have hr : (shiftTerm (.variable j) (k - e)).value ν =
        SignedRows.replacement j (k - e) ν := by
      rw [WindowProof.shifted_value]
      rfl
    rw [hr]
    constructor
    · rintro ⟨he, hg, hp⟩
      have hc := (actualGuardCalibration i j e h k l c _).mp hg
      exact ⟨(indexEquality_eval i j e h k l c _ hc).mp he, hc,
        (NormalFormSemanticProof.actualBooleanCompilation p _).mpr hp⟩
    · rintro ⟨he, hc, hp⟩
      exact ⟨(indexEquality_eval i j e h k l c _ hc).mpr he,
        (actualGuardCalibration i j e h k l c _).mpr hc,
        (NormalFormSemanticProof.actualBooleanCompilation p _).mp hp⟩

/-- Reuse the accepted quantitative source split; each of its three output
matrices now has an equivalent output in the restricted row grammar. -/
theorem actualTwoVariableElimination : HyperBranchRowsTargets.ActualTwoVariableElimination := by
  intro i j hij e h k l c p ν
  have hl (μ : Nat → Nat) :
      (HyperWindow.leftCases i j e h k l c p.compile).eval μ ↔
        (leftCases i j e h k l c p).eval μ :=
    (actualBranchCalibration i j e h k l c p μ).1.symm
  have hr (μ : Nat → Nat) :
      (HyperWindow.rightCases i j e h k l c p.compile).eval μ ↔
        (rightCases i j e h k l c p).eval μ :=
    (actualBranchCalibration i j e h k l c p μ).2.1.symm
  have he (μ : Nat → Nat) :
      (HyperWindow.equalCases i j e h k l c p.compile).eval μ ↔
        (equalCases i j e h k l c p).eval μ :=
    (actualBranchCalibration i j e h k l c p μ).2.2.symm
  have hb (μ : Nat → Nat) : p.compile.eval μ ↔ p.eval μ :=
    NormalFormSemanticProof.actualBooleanCompilation p μ
  simpa only [hb, hl, hr, he] using
    (HyperWindowProof.actualTwoVariableElimination i j hij e h k l c p.compile ν)

theorem closeGuard_variables (i j v : Nat) (e h k l : Int) (c : Nat) :
    v ∈ (closeGuard i j e h k l c).variables ↔ v = i ∨ v = j := by
  simp only [closeGuard, Formula.variables, List.mem_append,
    FiniteBranchRowsSemanticProof.guardedLe_variables, Summand.name]
  tauto

theorem indexEquality_variables (i j v : Nat) (e k : Int) :
    v ∈ (indexEquality i j e k).variables ↔ v = i ∨ v = j := by
  simp only [indexEquality, Formula.variables, Atom.row, rowVariables,
    List.map_cons, List.map_nil, Summand.name, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false]
  tauto

theorem exactBranchSupport : HyperBranchRowsTargets.ExactBranchSupport := by
  intro i j hij e h k l c p v
  refine ⟨?_, ?_, ?_⟩
  · rw [leftCases, BoundedRowsSemanticProof.exactBoundedSupport i
      (HyperWindow.leftBound e h l) (.conjunction (closeGuard i j e h k l c) p) v]
    have hpos : 0 < HyperWindow.leftBound e h l := by
      unfold HyperWindow.leftBound
      omega
    simp only [hpos, true_and, Formula.variables, List.mem_append, closeGuard_variables]
    tauto
  · rw [rightCases, BoundedRowsSemanticProof.exactBoundedSupport j
      (HyperWindow.rightBound h k l c) (.conjunction (closeGuard i j e h k l c) p) v]
    have hpos : 0 < HyperWindow.rightBound h k l c := by
      unfold HyperWindow.rightBound
      omega
    simp only [hpos, true_and, Formula.variables, List.mem_append, closeGuard_variables]
    tauto
  · rw [equalCases, SignedRowsSemanticProof.exactTotalSupport i j (k - e)
      (.conjunction (indexEquality i j e k) (.conjunction (closeGuard i j e h k l c) p)) v]
    simp only [Formula.variables, List.mem_append, indexEquality_variables, closeGuard_variables]
    have hnames : v = j → v ≠ i := by
      intro hv hvi
      exact hij (hvi.symm.trans hv)
    tauto

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperBranchRowsSemanticProof
