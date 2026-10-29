module
public import LogicLineages.OrdinalComparison.LimitPredecessorTargets
public import LogicLineages.OrdinalComparison.MaximumPredecessor
public import LogicLineages.OrdinalComparison.FiniteTail

@[expose] public section

namespace LogicLineages.OrdinalComparison

open Vendor.R1
open Order

theorem self_lt_finiteTail_one (a : NONote) : a < finiteTail a 1 := by
  change a.1.repr < (finiteTail a 1).1.repr
  rw [(finiteTailCorrect a 1).1, Nat.cast_one]
  exact lt_succ _

theorem finiteTail_lt_limit (a b : NONote) (hlim : IsSuccLimit a.1.repr)
    (hb : b < a) (n : Nat) : finiteTail b n < a := by
  change (finiteTail b n).1.repr < a.1.repr
  rw [(finiteTailCorrect b n).1]
  exact hlim.add_natCast_lt hb n

theorem limitMaximumPredecessorSaturation :
    Targets.LimitMaximumPredecessorSaturation maximumPredecessor := by
  intro a hlim budget
  have ha : (0 : NONote) < a := hlim.bot_lt
  have hm := maximumPredecessor_correct a budget ha
  apply Nat.le_antisymm hm.1.2
  by_contra hbudget
  have hs : treeWeight (finiteTail (maximumPredecessor a budget) 1).1 ≤ budget := by
    rw [(finiteTailCorrect (maximumPredecessor a budget) 1).2]
    omega
  have hmax := hm.2
    ⟨finiteTail_lt_limit a (maximumPredecessor a budget) hlim hm.1.1 1, hs⟩
  exact (not_le_of_gt (self_lt_finiteTail_one (maximumPredecessor a budget))) hmax

theorem limitMaximumPredecessorStrictGrowth :
    Targets.LimitMaximumPredecessorStrictGrowth maximumPredecessor := by
  intro a hlim b c hbc
  have ha : (0 : NONote) < a := hlim.bot_lt
  have hm := maximumPredecessor_correct a b ha
  have hc := maximumPredecessor_correct a c ha
  have hs : treeWeight (finiteTail (maximumPredecessor a b) 1).1 ≤ c := by
    rw [(finiteTailCorrect (maximumPredecessor a b) 1).2,
      limitMaximumPredecessorSaturation a hlim b]
    omega
  exact (self_lt_finiteTail_one (maximumPredecessor a b)).trans_le
    (hc.2 ⟨finiteTail_lt_limit a (maximumPredecessor a b) hlim hm.1.1 1, hs⟩)

end LogicLineages.OrdinalComparison
