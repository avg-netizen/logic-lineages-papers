module
public import LogicLineages.OrdinalComparison.AdjacentRangeWordGuardCompletion.Targets

@[expose] public section
namespace LogicLineages.OrdinalComparison.AdjacentRangeWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion CounterWordGuardCompletion

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

theorem adjacentHeadDecrease : Targets.AdjacentHeadDecrease := by
  intro A B n c e j k
  constructor
  · cases n <;> simp [innerWord,SourceRangeExpansion.lowerHead,counterNodes,List.filter_append,
      kernelLetter,quadraticLetter]
  · intro r
    unfold innerWord
    simp only [rangeNodes_append,rangeNodes_singleton,lower_rank]
    have hL : rangeRank (kernelLetter (n+3) (c+(n+3)) 0) = n+3 := by
      simp [rangeRank,kernelLetter]
    have hR : rangeRank (kernelLetter (n+3) c j) = n+3 := by
      simp [rangeRank,kernelLetter]
    rw [hL,hR]
    omega

end LogicLineages.OrdinalComparison.AdjacentRangeWordGuardCompletion.Proof
