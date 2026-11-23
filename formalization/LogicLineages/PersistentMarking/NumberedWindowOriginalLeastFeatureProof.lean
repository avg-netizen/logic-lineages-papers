module
public import LogicLineages.PersistentMarking.NumberedWindowClassAlgorithm
import Mathlib.Data.List.MinMax

public section
namespace LogicLineages.PersistentMarking.NumberedWindowOriginalLeastFeatureProof
open NumberedWindowClassAlgorithm (advance rounds members least)

private theorem memberAdvance (edge : Nat → Nat → Bool) (pool seen : List Nat) (v : Nat)
    (held : v ∈ advance edge pool seen) :
    ∃ w ∈ seen, w = v ∨ edge w v = true := by
  simp only [advance,List.mem_filter,List.any_eq_true,Bool.or_eq_true,beq_iff_eq] at held
  exact held.2

theorem exact_OriginalRoundPreservesFeature (edge : Nat → Nat → Bool)
    (pool : List Nat) (seed : Nat) (key : Nat → Nat)
    (transport : ∀ a b, edge a b = true → key b = key a) :
    ∀ n v, v ∈ rounds edge pool seed n → key v = key seed := by
  intro n
  induction n with
  | zero =>
    intro v haveV
    simp only [rounds,List.mem_filter,beq_iff_eq] at haveV
    exact congrArg key haveV.2.symm
  | succ n ih =>
    intro v haveV
    obtain ⟨w,old,step⟩ := memberAdvance edge pool (rounds edge pool seed n) v haveV
    rcases step with rfl | arc
    · exact ih _ old
    · exact (transport w v arc).trans (ih _ old)

/-- The actual returned minimum keeps any feature that the real
selected numeric exchange preserves. This uses the existing full
finite round tape and original min, not a substitute class relation. -/
theorem exact_OriginalLeastPreservesFeature (edge : Nat → Nat → Bool)
    (pool : List Nat) (seed y : Nat) (key : Nat → Nat)
    (transport : ∀ a b, edge a b = true → key b = key a)
    (result : least edge pool seed = some y) : key y = key seed := by
  change (members edge pool seed).min? = some y at result
  have present := (List.min?_eq_some_iff.mp result).1
  exact exact_OriginalRoundPreservesFeature edge pool seed key transport pool.length y present

#print axioms exact_OriginalRoundPreservesFeature
#print axioms exact_OriginalLeastPreservesFeature
end LogicLineages.PersistentMarking.NumberedWindowOriginalLeastFeatureProof
