module

public import LogicLineages.NativeModule.PersistentMarking.NativeRankPrefixTargets
public import LogicLineages.PersistentMarking.OrdinalRankSupportProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeRankPrefixChecks
open NativeIteratorStrictTargets NativeRankPrefixTargets OrdinalRankSupportProof

theorem exact_CountableNativeRankPrefixes : CountableNativeRankPrefixes := by
  intro codes S τ q h
  letI : Countable (ClosedNativeTerm S τ) := (codes S τ).countable
  exact exact_CountableRankPrefix h

#print axioms exact_CountableNativeRankPrefixes

end LogicLineages.PersistentMarking.NativeRankPrefixChecks
