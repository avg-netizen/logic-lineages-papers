import LogicLineages.PersistentMarking.NativeRankOrderTargets
import LogicLineages.PersistentMarking.NativeSyntaxCountabilityTargets

namespace LogicLineages.PersistentMarking.NativeRankPrefixTargets
open NativeIteratorStrictTargets NativeSyntaxCountabilityTargets

/-- The set of earlier stages of each actual same-type closed native rank. -/
def CountableNativeRankPrefixes : Prop :=
  ClosedNativeCountability →
    ∀ S τ (q : ClosedNativeTerm S τ) (h : Acc (@NativeBelow S τ) q),
      Countable {β : Ordinal.{0} // β < h.rank}

end LogicLineages.PersistentMarking.NativeRankPrefixTargets
