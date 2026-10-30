module
public import LogicLineages.OrdinalComparison.ControlResidueTargets
public import LogicLineages.OrdinalComparison.ControlComputability
public import LogicLineages.OrdinalComparison.Control

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem quadratic_le_two_pow (v : Nat) (hv : 1 ≤ v) : (v + 2) * v ≤ 2 ^ (v + 1) := by
  by_cases h1 : v = 1
  · subst v
    decide
  · have hv2 : 2 ≤ v := by omega
    induction v, hv2 using Nat.le_induction with
    | base => decide
    | succ n hn ih =>
      have h4 : 4 ≤ n * n := Nat.mul_le_mul hn hn
      have hp : (n + 1 + 2) * (n + 1) ≤ 2 * ((n + 2) * n) := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
        omega
      calc
        (n + 1 + 2) * (n + 1) ≤ 2 * ((n + 2) * n) := hp
        _ ≤ 2 * 2 ^ (n + 1) := Nat.mul_le_mul_left 2 (ih (by omega) (by omega))
        _ = 2 ^ (n + 1) * 2 := Nat.mul_comm _ _
        _ = 2 ^ (n + 1 + 1) := rfl

theorem fullFastControlHierarchyGrowth : Targets.FullFastControlHierarchyGrowth := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    exact ⟨(fixed_fastControl_primrec j).to_comp, fastControl_strictMono j,
      two_pow_le_fastControl j⟩
  · intro j n
    exact (two_pow_le_fastControl j _).trans (fastControl_step_growth j n)
  · intro A z hAz
    have hv : 1 ≤ Phi z := Nat.succ_le_of_lt ((Nat.zero_le z).trans_lt (self_lt_Phi z))
    have hAv : A ≤ Phi z := hAz.trans (self_lt_Phi z).le
    have hfactor : (A + 2) * Phi z ≤ (Phi z + 2) * Phi z :=
      Nat.mul_le_mul_right _ (Nat.add_le_add_right hAv 2)
    have hgap : 2 ^ (Phi z + 1) ≤ Phi (z + 1) := by
      have h := (two_pow_le_fastControl 4 _).trans (fastControl_step_growth 4 (z + 100))
      simpa only [Phi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    exact hfactor.trans ((quadratic_le_two_pow _ hv).trans hgap)

end LogicLineages.OrdinalComparison
