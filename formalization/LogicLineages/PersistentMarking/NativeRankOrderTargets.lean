import LogicLineages.PersistentMarking.NativeIteratorStrictTargets
import Mathlib.SetTheory.Ordinal.Rank

namespace LogicLineages.PersistentMarking.NativeRankOrderTargets
open NativeIteratorStrictTargets

def NativeRankRecurrence : Prop :=
  ∀ S τ (q : ClosedNativeTerm S τ) (h : Acc (@NativeBelow S τ) q),
    h.rank = ⨆ t : {t : ClosedNativeTerm S τ // NativeBelow t q}, Order.succ (h.inv t.2).rank

def NativeRankStrictEdge : Prop :=
  ∀ S τ (s t : ClosedNativeTerm S τ) (h : Acc (@NativeBelow S τ) s) (edge : NativeBelow t s),
    (h.inv edge).rank < h.rank

def NativeRankRestriction : Prop :=
  ∀ S τ (s : ClosedNativeTerm S τ) (h : Acc (@NativeBelow S τ) s)
    (full : Acc (fun t s : Spine.Expr => ConfinedPair.Strict S s t) s.val), h.rank ≤ full.rank

def NativeRankSuccessorWitness : Prop :=
  ∀ S τ (s : ClosedNativeTerm S τ) (h : Acc (@NativeBelow S τ) s) (β : Ordinal.{0}),
    Order.succ β ≤ h.rank →
      ∃ (t : ClosedNativeTerm S τ) (edge : NativeBelow t s), β ≤ (h.inv edge).rank

end LogicLineages.PersistentMarking.NativeRankOrderTargets
