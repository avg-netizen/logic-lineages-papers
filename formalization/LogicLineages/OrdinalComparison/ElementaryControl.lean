module
public import LogicLineages.OrdinalComparison.ElementaryControlTargets
public import LogicLineages.OrdinalComparison.Control
public import LogicLineages.OrdinalComparison.ControlComputability

@[expose] public section

/-! The complete elementary-control lemma, including encoded computability
and its stated final linear-gap consequence. -/

namespace LogicLineages.OrdinalComparison

theorem four_mul_add_four_lt_two_pow_succ {a : Nat} (ha : 4 ≤ a) :
    4 * a + 4 < 2 ^ (a + 1) := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
      calc
        4 * (n + 1) + 4 < 2 ^ (n + 1) + 2 ^ (n + 1) := by omega
        _ = 2 ^ (n + 1 + 1) := by rw [Nat.pow_succ]; omega

theorem four_le_Phi (n : Nat) : 4 ≤ Phi n := by
  exact (show 4 = 2 ^ 2 by decide).le.trans
    ((Nat.pow_le_pow_right (by decide) (by omega : 2 ≤ n + 100)).trans
      (two_pow_shift_le_Phi n))

theorem Phi_linear_gap (n : Nat) : 4 * Phi n + 4 < Phi (n + 1) := by
  have hexp : Phi n + 1 ≤ 2 ^ Phi n :=
    Nat.succ_le_of_lt Nat.lt_two_pow_self
  exact ((four_mul_add_four_lt_two_pow_succ (four_le_Phi n)).trans_le
    (Nat.pow_le_pow_right (by decide) hexp)).trans_le (Phi_double_tower_gap n)

theorem elementaryControlProperties : Targets.ElementaryControlProperties :=
  ⟨Phi_computable, Phi_strictMono, fun n =>
    ⟨self_lt_Phi n, Phi_double_tower_gap n, Phi_linear_gap n⟩⟩

end LogicLineages.OrdinalComparison
