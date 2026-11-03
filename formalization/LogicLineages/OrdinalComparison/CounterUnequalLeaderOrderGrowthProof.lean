module
public import LogicLineages.OrdinalComparison.CounterUnequalLeaderOrderTargets
public import LogicLineages.OrdinalComparison.Control

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterUnequalLeaderOrder.Proof
open CounterLeaderExpansion

theorem actualLeaderGap : Targets.ActualLeaderGap := by
  intro n m c e t u h
  let a := leaderPreimage n c t
  let b := leaderPreimage m e u
  change Phi a < Phi b at h
  have hab : a < b := by
    by_contra hn
    have hm := Phi_strictMono.monotone (Nat.le_of_not_gt hn)
    exact (not_le_of_gt h) hm
  have hex : 2^(Phi a+1) ≤ 2^(2^(Phi a+1)) :=
    Nat.pow_le_pow_right (by decide) (Nat.lt_two_pow_self (n := Phi a+1)).le
  have hm := Phi_strictMono.monotone (Nat.succ_le_of_lt hab)
  exact hex.trans ((Phi_succ_gap a).trans hm)

end LogicLineages.OrdinalComparison.CounterUnequalLeaderOrder.Proof
