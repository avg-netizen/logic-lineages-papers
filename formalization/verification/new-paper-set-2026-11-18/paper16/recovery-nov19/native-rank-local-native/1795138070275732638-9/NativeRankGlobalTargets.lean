import LogicLineages.PersistentMarking.NativeRankTargets

namespace LogicLineages.PersistentMarking.NativeRankGlobalTargets
open NativeIteratorStrictTargets NativeRankTargets
open scoped Ordinal

/-- The rank assertions for every original closed native term and the
actual global relation. The two accessibility witnesses are supplied
by genuine well-foundedness of these two relations. -/
def ActualClosedNativeRanks : Prop :=
  ∀ S τ,
    ∃ nativeWF : WellFounded (@NativeBelow S τ),
    ∃ confinedWF : WellFounded (fun t s : Spine.Expr => ConfinedPair.Strict S s t),
    ∀ s : ClosedNativeTerm S τ,
      nativeRank (nativeWF.apply s) < ω₁ ∧
      nativeRank (nativeWF.apply s) ≤ confinedRank (confinedWF.apply s.val) ∧
      nativeRank (nativeWF.apply s) =
        (⨆ t : {t : ClosedNativeTerm S τ // NativeBelow t s},
          Order.succ (nativeRank (nativeWF.apply t.val))) ∧
      (∀ t : ClosedNativeTerm S τ, NativeBelow t s →
        nativeRank (nativeWF.apply t) < nativeRank (nativeWF.apply s)) ∧
      (∀ β : Ordinal.{0}, Order.succ β ≤ nativeRank (nativeWF.apply s) →
        ∃ t : ClosedNativeTerm S τ, NativeBelow t s ∧ β ≤ nativeRank (nativeWF.apply t))

end LogicLineages.PersistentMarking.NativeRankGlobalTargets
