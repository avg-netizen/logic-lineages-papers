module
public import LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion.Targets
public import LogicLineages.OrdinalComparison.RangePhiFactorization.HeadProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion CounterWordGuardCompletion

theorem rangeHeadPreimage : Targets.RangeHeadPreimage := by
  intro D a t ha hr ht
  by_cases h1 : a.1 = 1
  · simp [preimageWord,h1,WordAllowed,WordDomain,LetterDomain,letterValue,wordValue]
  · have hRange : RangePhiFactorization.RangeHead a := by
      rcases hr with h | h
      · exact False.elim (h1 h)
      · exact h
    have hh := RangePhiFactorization.Proof.headFactorization D a t ha hRange ht
    have hp := (RangePhiFactorization.Proof.predecessorHeadSyntax D a ha hRange).1
    rw [preimageWord,if_neg h1]
    exact ⟨RangePhiFactorization.Proof.singleton_allowed D _ hp,
      ⟨hh.2.1,trivial⟩,hh.1,hh.2.2⟩

private theorem counterNodes_append (A B : Word) :
    counterNodes (A++B) = counterNodes A+counterNodes B := by
  simp [counterNodes,List.filter_append]

private theorem leader_no_counters (n c : Nat) : counterNodes (leaderWord n c) = 0 := by
  induction n with
  | zero => simp [leaderWord,counterNodes,kernelLetter]
  | succ n ih => simpa [leaderWord,counterNodes,kernelLetter] using ih

private theorem range_no_counters (a : Letter) (hr : RangeHead a) :
    counterNodes [a] = 0 ∧ counterNodes (preimageWord a) = 0 := by
  rcases hr with h | h | h
  · simp [counterNodes,preimageWord,h]
  · simp [counterNodes,preimageWord,RangePhiFactorization.predecessorHead,h]
  · simp [counterNodes,preimageWord,RangePhiFactorization.predecessorHead,h]

theorem counterHeadDecrease : Targets.CounterHeadDecrease := by
  intro A B a hr n c
  have hz := range_no_counters a hr
  simp only [rangeInputWord,counterNodes_append,leader_no_counters,hz.1,hz.2]
  simp [counterNodes,counterLetter]
  omega

end LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion.Proof
