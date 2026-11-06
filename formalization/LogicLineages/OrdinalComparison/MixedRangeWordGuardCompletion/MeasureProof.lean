module
public import LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.Targets

@[expose] public section
namespace LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion CounterWordGuardCompletion AdjacentRangeWordGuardCompletion

private theorem rangeNodes_append (r : Nat) (A B : Word) :
    rangeNodes r (A++B) = rangeNodes r A+rangeNodes r B := by
  simp [rangeNodes,List.filter_append]

private theorem rangeNodes_singleton (r : Nat) (a : Letter) :
    rangeNodes r [a] = if r=rangeRank a then 1 else 0 := by
  by_cases h : r=rangeRank a
  · simp [rangeNodes,h]
  · have h' : rangeRank a ≠ r := Ne.symm h
    simp [rangeNodes,h,h']

private theorem lower_rank (n e : Nat) (k : Int) :
    rangeRank (SourceRangeExpansion.lowerHead n e k) = n+2 := by
  cases n <;> simp [SourceRangeExpansion.lowerHead,rangeRank,kernelLetter,quadraticLetter]

private theorem prefix_counter (n m c : Nat) :
    counterNodes (FiniteRangeExposure.exposurePrefix n m c) = 0 := by
  induction m with
  | zero => simp [FiniteRangeExposure.exposurePrefix,counterNodes,kernelLetter]
  | succ m ih => simpa [FiniteRangeExposure.exposurePrefix,counterNodes,kernelLetter] using ih

/-- Every retained rank occurs exactly once, not merely somewhere in a bounded interval. -/
theorem prefix_range_count (n m c r : Nat) :
    rangeNodes r (FiniteRangeExposure.exposurePrefix n m c) =
      if n+3 ≤ r ∧ r ≤ n+m+3 then 1 else 0 := by
  induction m with
  | zero =>
      change rangeNodes r [kernelLetter (n+3) (c+(n+3)) 0] = _
      rw [rangeNodes_singleton]
      have hr : rangeRank (kernelLetter (n+3) (c+(n+3)) 0) = n+3 := by simp [rangeRank,kernelLetter]
      rw [hr]
      split_ifs <;> omega
  | succ m ih =>
      change rangeNodes r ([kernelLetter (n+m+4) (c+(n+m+4)) 0]++FiniteRangeExposure.exposurePrefix n m c) = _
      rw [rangeNodes_append,rangeNodes_singleton,ih]
      have hr : rangeRank (kernelLetter (n+m+4) (c+(n+m+4)) 0) = n+m+4 := by simp [rangeRank,kernelLetter]
      rw [hr]
      split_ifs <;> omega

theorem mixedHeadDecrease : Targets.MixedHeadDecrease := by
  intro A B n m c e j k
  have hC (P Q : Word) : counterNodes (P++Q) = counterNodes P+counterNodes Q := by
    simp [counterNodes,List.filter_append]
  constructor
  · simp only [retainedWord,hC,prefix_counter]
    cases n <;> simp [SourceRangeExpansion.lowerHead,counterNodes,kernelLetter,quadraticLetter]
  · intro r
    simp only [retainedWord,rangeNodes_append,rangeNodes_singleton,prefix_range_count,lower_rank]
    have hr : rangeRank (kernelLetter (n+m+3) c j) = n+m+3 := by simp [rangeRank,kernelLetter]
    rw [hr]
    split_ifs <;> omega

end LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.Proof
