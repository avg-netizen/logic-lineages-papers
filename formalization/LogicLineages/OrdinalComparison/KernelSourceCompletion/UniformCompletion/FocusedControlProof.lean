module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.FocusedSupplierTargets
public import LogicLineages.OrdinalComparison.Control
public import Mathlib.Algebra.Ring.Parity

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Focused

/-! Source-preserving extraction of CounterLeaderBoundsGrowthProof.four_mul_lt_Phi and the direct power-of-two / parity argument in CounterLeaderExpansionSuppliersProof. No control residue or totient theorem is imported. -/

/-- A whole-domain consequence of the literal control's shifted exponential bound. -/
theorem four_mul_lt_Phi  : FocusedSupplierTargets.FourMulControl := by
  intro u
  have hp : 4*u < 2^(u+2) := by
    have h := Nat.mul_lt_mul_of_pos_left (Nat.lt_two_pow_self (n := u)) (by decide : 0 < 4)
    simpa [pow_add, Nat.mul_comm] using h
  have hm : 2^(u+2) ≤ 2^(u+100) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  exact hp.trans_le (hm.trans (two_pow_shift_le_Phi u))

private theorem control_power_of_two (j n : Nat) :
    ∃ k : Nat, fastControl j n = 2 ^ k := by
  induction j generalizing n with
  | zero => exact ⟨n, rfl⟩
  | succ j ih =>
    change ∃ k : Nat, (fastControl j)^[n + 1] n = 2 ^ k
    rw [Function.iterate_succ_apply']
    exact ih _

theorem actualPhiEven : FocusedSupplierTargets.PhiEven := by
  intro t
  obtain ⟨k, hk⟩ := control_power_of_two 5 (t + 100)
  have hlarge : 1 < fastControl 5 (t + 100) := by
    have h := self_lt_fastControl 5 (t + 100)
    omega
  have hn : k ≠ 0 := by
    intro hz
    rw [hz, pow_zero] at hk
    omega
  change Even (fastControl 5 (t + 100))
  rw [hk]
  exact even_two.pow_of_ne_zero hn

end LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Focused
