import LogicLineages.PersistentMarking.ComparisonTargets
namespace LogicLineages.PersistentMarking.ComparisonFoundationProof
open Spine

theorem fixedRankedArity : ComparisonTargets.FixedRankedArity := by
  intro S name a b ha hb
  rcases ha with ⟨m, hm⟩
  rcases hb with ⟨n, hn⟩
  cases he : lookupRank S.entries name with
  | none => simp [classRank, he] at hm
  | some p =>
    rcases p with ⟨arity, i⟩
    by_cases ha : a = arity
    · by_cases hb : b = arity
      · exact ha.trans hb.symm
      · simp [classRank, he, hb] at hn
    · simp [classRank, he, ha] at hm

theorem nativeEquivalent : ComparisonTargets.NativeEquivalent := by
  intro S σ τ
  exact ⟨1, rfl, rfl⟩

theorem nativeAboveApplication : ComparisonTargets.NativeAboveApplication := by
  intro S σ τ
  exact ⟨1, 0, rfl, rfl, by decide⟩

theorem rankedAboveNative : ComparisonTargets.RankedAboveNative := by
  intro S name arity σ ha
  rcases ha with ⟨n, hn⟩
  cases he : lookupRank S.entries name with
  | none => simp [classRank, he] at hn
  | some p =>
    rcases p with ⟨a,i⟩
    by_cases h : arity = a
    · exact ⟨i+2, 1, by simp [classRank, he, h], rfl, by omega⟩
    · simp [classRank, he, h] at hn

theorem removeLength (xs : Args) (x : Expr) (ys : Args) (h : Remove xs x ys) :
    xs.length = ys.length+1 := by
  induction h with
  | here => simp [Args.length, Nat.add_comm]
  | there _ ih => simp [Args.length, ih, Nat.add_assoc]

theorem splitLength (xs ys zs : Args) (h : Split xs ys zs) :
    xs.length = ys.length+zs.length := by
  induction h with
  | nil => rfl
  | left _ ih => simp [Args.length, ih, Nat.add_assoc]
  | right _ ih => simp [Args.length, ih]; omega
end LogicLineages.PersistentMarking.ComparisonFoundationProof
