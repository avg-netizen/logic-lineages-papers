module
public import LogicLineages.OrdinalComparison.ParametricCoefficientOneTargets
public import LogicLineages.OrdinalComparison.ParametricActualCollapseProof
public import LogicLineages.OrdinalComparison.ActualFiniteHead
public import LogicLineages.OrdinalComparison.ActualCollapseBounds
public import LogicLineages.OrdinalComparison.PolynomialPartitionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.ParametricCoefficientOne.Proof

theorem omega_tail_facts (n : Nat) :
    Ordinal.omega0+(n : Ordinal) < epsilonZero ∧
    actualOrdinalNorm (Ordinal.omega0+(n : Ordinal)) = n+2 := by
  have hw : Ordinal.omega0 < epsilonZero := by
    simpa only [Nat.cast_one,Ordinal.opow_one] using finiteOmegaPowerBelowEpsilonZero 1
  refine ⟨(actualFiniteTailClosureNorm _ hw n).1,?_⟩
  simpa only [Nat.cast_one,mul_one,Nat.mul_one,Nat.add_comm] using actualFiniteHeadNorm 1 n

theorem predecessor_split (n : Nat) (x : Ordinal) (hx : x < Ordinal.omega0+(n : Ordinal)) :
    (∃ k : Nat, x = (k : Ordinal)) ∨
    (∃ k : Nat, k<n ∧ x = Ordinal.omega0+(k : Ordinal)) := by
  have ht : Ordinal.omega0+(n : Ordinal) < Ordinal.omega0*(2 : Ordinal) := by
    simpa only [show (2 : Ordinal)=1+1 from one_add_one_eq_two.symm,mul_add,mul_one] using
      (add_lt_add_right (Ordinal.natCast_lt_omega0 n) Ordinal.omega0)
  obtain ⟨q,hq,r,hr,heq⟩ := Ordinal.lt_mul_iff.mp (hx.trans ht)
  obtain ⟨j,hj⟩ := Ordinal.eq_natCast_of_le_natCast hq.le
  obtain ⟨k,hk⟩ := Ordinal.lt_omega0.mp hr
  rw [hj,hk] at heq
  have hj2 : j<2 := by rw [hj] at hq; exact_mod_cast hq
  rcases (show j=0 ∨ j=1 by omega) with rfl | rfl
  · left
    refine ⟨k,?_⟩
    simpa only [Nat.cast_zero,mul_zero,zero_add] using heq
  · right
    have hx' : Ordinal.omega0+(k : Ordinal) < Ordinal.omega0+(n : Ordinal) := by
      simpa only [heq,Nat.cast_one,mul_one] using hx
    refine ⟨k,?_,?_⟩
    · have hh : (k : Ordinal)<(n : Ordinal) := (add_lt_add_iff_left _).mp hx'
      exact_mod_cast hh
    · simpa only [Nat.cast_one,mul_one] using heq
end LogicLineages.OrdinalComparison.ParametricCoefficientOne.Proof
