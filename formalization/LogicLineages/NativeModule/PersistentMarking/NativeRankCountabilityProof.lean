module

public import LogicLineages.NativeModule.PersistentMarking.NativeRankOrderProof
public import Mathlib.SetTheory.Cardinal.Regular

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeRankCountabilityProof
open NativeIteratorStrictTargets NativeRankTargets
open scoped Ordinal

theorem countableRanks : CountableNativeRanks := by
  intro codes S τ q h
  letI : Countable (ClosedNativeTerm S τ) := (codes S τ).countable
  induction h with
  | intro q pred ih =>
    rw [NativeRankOrderProof.recurrence S τ q (Acc.intro q pred)]
    apply Ordinal.iSup_lt_omega_one
    intro t
    exact (Cardinal.isSuccLimit_omega (1 : Ordinal)).succ_lt (ih t.val t.property)

end LogicLineages.PersistentMarking.NativeRankCountabilityProof
