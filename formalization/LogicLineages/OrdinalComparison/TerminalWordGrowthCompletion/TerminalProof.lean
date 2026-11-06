module
public import LogicLineages.OrdinalComparison.TerminalWordGrowthCompletion.WordProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminalWordGrowthCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion

private theorem two_mul_le_two_pow (n : Nat) (hn : 1 ≤ n) : 2*n ≤ 2^n := by
  cases n with
  | zero => omega
  | succ k =>
      have hk : k+1 ≤ 2^k := Nat.lt_two_pow_self
      have hh := Nat.mul_le_mul_left 2 hk
      simpa only [Nat.succ_eq_add_one,pow_succ,Nat.mul_comm] using hh

theorem terminalGuard : Targets.TerminalGuard := by
  intro D w x y b hw hnon hx hy hyx
  have hg := wordGrowth D w x hw hnon ((Nat.le_max_left _ _).trans hx)
  have hx' : 2*growthOffset w+b.natAbs+2 ≤ x :=
    (Nat.le_max_right _ _).trans hx
  have hy' : 2*growthOffset w+b.natAbs+2 ≤ y :=
    (Nat.le_max_right _ _).trans hy
  have hb : -(b.natAbs : Int) ≤ b ∧ b ≤ (b.natAbs : Int) := by
    cases b <;> simp <;> omega
  have hdom : 0 ≤ (y : Int)+b := by omega
  refine ⟨hg.1,⟨hdom,trivial⟩,?_⟩
  change ((y : Int)+b).toNat < wordValue w x
  have hleaf : ((y : Int)+b).toNat ≤ y+b.natAbs := by omega
  have hlin : x+b.natAbs < 2*(x-growthOffset w) := by omega
  have hpow := two_mul_le_two_pow (x-growthOffset w) (by omega)
  omega

end LogicLineages.OrdinalComparison.TerminalWordGrowthCompletion.Proof
