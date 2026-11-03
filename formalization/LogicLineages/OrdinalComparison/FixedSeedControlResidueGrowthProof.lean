module
public import LogicLineages.OrdinalComparison.FixedSeedControlResidueTargets
public import LogicLineages.OrdinalComparison.Control

@[expose] public section
namespace LogicLineages.OrdinalComparison.FixedSeedControlResidue.Proof

theorem h_zero : H 0 = 1 := rfl

theorem h_succ (n : Nat) : H (n + 1) = Phi (H n) := by
  unfold H
  rw [Function.iterate_succ_apply']

theorem h_lower_bound (n : Nat) : n + 1 ≤ H n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [h_succ]
    have hg := self_lt_Phi (H n)
    omega

theorem h_strictMono : StrictMono H := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [h_succ]
  exact self_lt_Phi (H n)

theorem literalRecursionAndGrowth : Targets.LiteralRecursionAndGrowth :=
  ⟨h_zero, h_succ, h_lower_bound, h_strictMono⟩

end LogicLineages.OrdinalComparison.FixedSeedControlResidue.Proof
