module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteBranchRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearWindowProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ActiveHyperProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteBranchRowsSemanticProof
open NormalForm FiniteBranchRows

theorem nonlinear_name (i : Nat) (kind : Bool) (e h : Int) :
    (nonlinear i kind e h).name = i := by
  cases kind <;> rfl

theorem nonlinear_term (i : Nat) (kind : Bool) (e h : Int) :
    (nonlinear i kind e h).term = LinearWindow.valueTerm i kind e h := by
  cases kind <;> rfl

theorem shiftDomain_eval (a : Term) (e : Int) (ν : Nat → Nat) :
    (shiftDomain a e).eval ν ↔ 0 ≤ (a.value ν : Int) + e := by
  simp only [shiftDomain, Matrix.eval, Term.value, not_lt]
  omega

theorem phi_meaningful (i : Nat) (e : Int) (ν : Nat → Nat) :
    (Summand.phi i e).meaningful ν ↔ (shiftDomain (.variable i) e).eval ν := by
  rw [shiftDomain_eval]
  rfl

theorem hyper_meaningful (i : Nat) (e h : Int) (ν : Nat → Nat) :
    (Summand.hyperPhi i e h).meaningful ν ↔ (HyperWindow.domainMatrix i e h).eval ν := by
  simp only [Summand.meaningful, HyperWindow.domainMatrix, Matrix.eval,
    shiftDomain_eval, HyperWindow.indexTerm, Term.value, WindowProof.shifted_value]

theorem nonlinear_meaningful (i : Nat) (kind : Bool) (e h : Int) (ν : Nat → Nat) :
    (nonlinear i kind e h).meaningful ν ↔ (LinearWindow.domainMatrix i kind e h).eval ν := by
  cases kind with
  | false =>
      simpa only [nonlinear, LinearWindow.domainMatrix, Bool.false_eq_true, ↓reduceIte]
        using phi_meaningful i e ν
  | true =>
      simpa only [nonlinear, LinearWindow.domainMatrix, ↓reduceIte]
        using hyper_meaningful i e h ν

theorem leRow_meaningful (s t : Summand) (c : Nat) (ν : Nat → Nat) :
    rowMeaningful (leRow s t c) ν ↔ s.meaningful ν ∧ t.meaningful ν := by
  constructor
  · intro h
    exact ⟨h (-1, s) (by simp [leRow]), h ((c : Int), t) (by simp [leRow])⟩
  · rintro ⟨hs, ht⟩ a ha
    simp only [leRow, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact hs
    · exact ht

theorem leRow_nonnegative (s t : Summand) (c : Nat) (ν : Nat → Nat) :
    0 ≤ rowValue (leRow s t c) ν ↔ s.term.value ν ≤ c * t.term.value ν := by
  simp only [leRow, rowValue, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, neg_one_mul, add_zero, zero_add, ← Int.natCast_mul]
  omega

/-- Every original occurrence domain is retained, including the right-hand
occurrence when its coefficient is zero. -/
theorem guardedLe_eval (s t : Summand) (c : Nat) (ν : Nat → Nat) :
    (guardedLe s t c).eval ν ↔
      s.meaningful ν ∧ t.meaningful ν ∧ s.term.value ν ≤ c * t.term.value ν := by
  change ((domainFormula (leRow s t c)).eval ν ∧ 0 ≤ rowValue (leRow s t c) ν) ↔ _
  rw [NormalFormSemanticProof.exactOriginalRowDomains (leRow s t c) ν,
    leRow_meaningful, leRow_nonnegative]
  simp only [and_assoc]

/-- The restricted-row guard is exactly the existing source guard, with all
original signed domains and both correlated comparisons. -/
theorem linearGuard_eval (i j : Nat) (leftKind rightKind : Bool)
    (e h k l : Int) (a : Nat) (ν : Nat → Nat) :
    (linearGuard i j leftKind rightKind e h k l a).eval ν ↔
      (LinearWindow.guard i j leftKind rightKind e h k l a).eval ν := by
  simp only [linearGuard, Formula.eval, guardedLe_eval, nonlinear_meaningful, nonlinear_term]
  simp only [Summand.meaningful, Summand.term, Term.value, Nat.one_mul,
    LinearWindow.guard, Matrix.eval, atMost, not_lt]
  tauto

theorem activeGuard_eval (i j : Nat) (kind : Bool)
    (e h k l q : Int) (a : Nat) (ν : Nat → Nat) :
    (activeGuard i j kind e h k l q a).eval ν ↔
      (ActiveHyper.guard i j kind e h k l q a).eval ν := by
  simp only [activeGuard, Formula.eval, guardedLe_eval, nonlinear_meaningful,
    hyper_meaningful, phi_meaningful, nonlinear_term]
  simp only [Summand.term, Term.value, Nat.one_mul, ActiveHyper.guard, Matrix.eval, atMost, not_lt]
  tauto

theorem actualLinearBranchElimination : FiniteBranchRowsTargets.ActualLinearBranchElimination := by
  intro i j leftKind rightKind e h k l a p ν
  rw [linearCases, BoundedRowsSemanticProof.actualBoundedElimination j
    (LinearWindow.bound rightKind k l a)
    (.conjunction (linearGuard i j leftKind rightKind e h k l a) p) ν]
  constructor
  · rintro ⟨n, _, hg, hp⟩
    exact ⟨n, (linearGuard_eval i j leftKind rightKind e h k l a _).mp hg, hp⟩
  · rintro ⟨n, hg, hp⟩
    have hn := LinearWindowProof.actualGuardBound i j leftKind rightKind e h k l a
      (Function.update ν j n) hg
    refine ⟨n, ?_, (linearGuard_eval i j leftKind rightKind e h k l a _).mpr hg, hp⟩
    simpa only [Function.update_self] using hn

theorem actualActiveHyperBranchElimination :
    FiniteBranchRowsTargets.ActualActiveHyperBranchElimination := by
  intro i j kind e h k l q a p ν
  rw [activeCases, BoundedRowsSemanticProof.actualBoundedElimination j
    (ActiveHyper.bound k l q a) (.conjunction (activeGuard i j kind e h k l q a) p) ν]
  constructor
  · rintro ⟨n, _, hg, hp⟩
    exact ⟨n, (activeGuard_eval i j kind e h k l q a _).mp hg, hp⟩
  · rintro ⟨n, hg, hp⟩
    have hn := ActiveHyperProof.actualGuardBound i j kind e h k l q a
      (Function.update ν j n) hg
    refine ⟨n, ?_, (activeGuard_eval i j kind e h k l q a _).mpr hg, hp⟩
    simpa only [Function.update_self] using hn

theorem guardedLe_variables (s t : Summand) (c v : Nat) :
    v ∈ (guardedLe s t c).variables ↔ v = s.name ∨ v = t.name := by
  simp only [guardedLe, guardedAtom, leRow, domainFormula, List.foldr_cons,
    List.foldr_nil, Formula.variables, Atom.row, rowVariables, domainRow,
    List.map_cons, List.map_nil, Summand.name, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false]
  tauto

theorem linearGuard_variables (i j : Nat) (leftKind rightKind : Bool)
    (e h k l : Int) (a v : Nat) :
    v ∈ (linearGuard i j leftKind rightKind e h k l a).variables ↔ v = i ∨ v = j := by
  simp only [linearGuard, Formula.variables, List.mem_append, guardedLe_variables, nonlinear_name]
  simp only [Summand.name]
  tauto

theorem activeGuard_variables (i j : Nat) (kind : Bool)
    (e h k l q : Int) (a v : Nat) :
    v ∈ (activeGuard i j kind e h k l q a).variables ↔ v = i ∨ v = j := by
  simp only [activeGuard, Formula.variables, List.mem_append, guardedLe_variables, nonlinear_name]
  simp only [Summand.name]
  tauto

theorem exactBranchSupport : FiniteBranchRowsTargets.ExactBranchSupport := by
  constructor
  · intro i j leftKind rightKind e h k l a p v
    rw [linearCases, BoundedRowsSemanticProof.exactBoundedSupport j
      (LinearWindow.bound rightKind k l a)
      (.conjunction (linearGuard i j leftKind rightKind e h k l a) p) v]
    have hpos : 0 < LinearWindow.bound rightKind k l a := by
      unfold LinearWindow.bound
      omega
    simp only [hpos, true_and, Formula.variables, List.mem_append, linearGuard_variables]
    tauto
  · intro i j kind e h k l q a p v
    rw [activeCases, BoundedRowsSemanticProof.exactBoundedSupport j
      (ActiveHyper.bound k l q a) (.conjunction (activeGuard i j kind e h k l q a) p) v]
    have hpos : 0 < ActiveHyper.bound k l q a := by
      unfold ActiveHyper.bound
      omega
    simp only [hpos, true_and, Formula.variables, List.mem_append, activeGuard_variables]
    tauto

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteBranchRowsSemanticProof
