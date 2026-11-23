module

public import LogicLineages.NativeModule.PersistentMarking.NativeSyntaxCountabilityTargets
public import Mathlib.SetTheory.Ordinal.Rank
public import Mathlib.SetTheory.Cardinal.Aleph

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeRankTargets
open NativeIteratorStrictTargets NativeSyntaxCountabilityTargets
open scoped Ordinal

/-- The actual rank in the same-type closed native restriction.
Accessibility is supplied by the checked well-foundedness of NativeBelow. -/
noncomputable def nativeRank {S τ} {q : ClosedNativeTerm S τ}
    (h : Acc (@NativeBelow S τ) q) : Ordinal.{0} :=
  h.rank

/-- The rank of the same syntax in the original full confined strict relation. -/
noncomputable def confinedRank {S} {q : Spine.Expr}
    (h : Acc (fun t s : Spine.Expr => ConfinedPair.Strict S s t) q) : Ordinal.{0} :=
  h.rank

def NativeRankRecurrence : Prop :=
  ∀ S τ (q : ClosedNativeTerm S τ) (h : Acc (@NativeBelow S τ) q),
    nativeRank h =
      ⨆ t : {t : ClosedNativeTerm S τ // NativeBelow t q}, Order.succ (nativeRank (h.inv t.2))

def NativeRankStrictEdge : Prop :=
  ∀ S τ (s t : ClosedNativeTerm S τ) (h : Acc (@NativeBelow S τ) s) (edge : NativeBelow t s),
    nativeRank (h.inv edge) < nativeRank h

def NativeRankRestriction : Prop :=
  ∀ S τ (s : ClosedNativeTerm S τ) (h : Acc (@NativeBelow S τ) s)
    (full : Acc (fun t s : Spine.Expr => ConfinedPair.Strict S s t) s.val),
    nativeRank h ≤ confinedRank full

def NativeRankSuccessorWitness : Prop :=
  ∀ S τ (s : ClosedNativeTerm S τ) (h : Acc (@NativeBelow S τ) s) (β : Ordinal.{0}),
    Order.succ β ≤ nativeRank h →
      ∃ (t : ClosedNativeTerm S τ) (edge : NativeBelow t s), β ≤ nativeRank (h.inv edge)

def CountableNativeRanks : Prop :=
  ClosedNativeCountability →
    ∀ S τ (q : ClosedNativeTerm S τ) (h : Acc (@NativeBelow S τ) q), nativeRank h < ω₁

end LogicLineages.PersistentMarking.NativeRankTargets
