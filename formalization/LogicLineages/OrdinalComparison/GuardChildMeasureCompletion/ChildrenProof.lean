module
public import LogicLineages.OrdinalComparison.GuardChildMeasureCompletion.InvariantProof
public import LogicLineages.OrdinalComparison.CounterWordGuardCompletion.LeaderProof
public import LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion.HeadProof
public import LogicLineages.OrdinalComparison.ShiftedPhiRangeWordGuardCompletion.WordProof
public import LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.MeasureProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.GuardChildMeasureCompletion.Proof
open PolynomialGraphCompletion CounterWordGuardCompletion CounterRangeWordGuardCompletion
open AdjacentRangeWordGuardCompletion MixedRangeWordGuardCompletion

private theorem shifted_heads_measure (D : Nat) (A B : Word) (a b : Letter) (j k : Int) :
    wordMeasure D (A++[a,shiftLetter j],B++[b,shiftLetter k]) =
      wordMeasure D (A++[a],B++[b]) := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using
    measure_shifts D (A++[a]) (B++[b]) j k

private theorem decrease_shifted_heads (D : Nat) (next : WordPair)
    (A B : Word) (a b : Letter) (j k : Int)
    (h : ChildDecrease D next (A++[a],B++[b])) :
    ChildDecrease D next (A++[a,shiftLetter j],B++[b,shiftLetter k]) := by
  unfold ChildDecrease
  rw [shifted_heads_measure]
  exact h

private theorem counter_counter_decrease (D : Nat) (A B : Word)
    (n m c e : Nat) (j k : Int) :
    ChildDecrease D (A++leaderWord n c,B++leaderWord m e)
      (A++[counterLetter (n+3) c,shiftLetter j],B++[counterLetter (m+3) e,shiftLetter k]) := by
  apply decrease_shifted_heads
  apply decrease_of_counter
  have h := CounterWordGuardCompletion.Proof.counterHeadDecrease A B n m c e
  change counterNodes (A++leaderWord n c)+counterNodes (B++leaderWord m e) <
    counterNodes (A++[counterLetter (n+3) c])+counterNodes (B++[counterLetter (m+3) e])
  omega

private theorem counter_range_decrease (D : Nat) (A B : Word)
    (a : Letter) (n c : Nat) (j k : Int) (hr : RangeHead a) :
    ChildDecrease D (A++leaderWord n c,rangeInputWord B a)
      (A++[counterLetter (n+3) c,shiftLetter j],B++[a,shiftLetter k]) := by
  apply decrease_shifted_heads
  apply decrease_of_counter
  have h := CounterRangeWordGuardCompletion.Proof.counterHeadDecrease A B a hr n c
  change counterNodes (A++leaderWord n c)+counterNodes (rangeInputWord B a) <
    counterNodes (A++[counterLetter (n+3) c])+counterNodes (B++[a])
  omega

private theorem phi_range_decrease (D : Nat) (A B : Word)
    (a : Letter) (j k : Int) (ha : LetterAllowed D a) (hr : RangeHead a) :
    ChildDecrease D (A,rangeInputWord B a)
      (A++[phiLetter,shiftLetter j],B++[a,shiftLetter k]) := by
  apply decrease_shifted_heads
  apply decrease_of_rank D _ _ 1
  · exact (ShiftedPhiRangeWordGuardCompletion.Proof.headDecrease A B a hr).1
  · omega
  · unfold rankBound
    omega
  · rcases hr with h | h | h
    · simp [rangeCount,rangeNodes,rangeRank,rangeInputWord,preimageWord,
        RangePhiFactorization.predecessorHead,List.filter_append,phiLetter,h] <;> omega
    · simp [rangeCount,rangeNodes,rangeRank,rangeInputWord,preimageWord,
        RangePhiFactorization.predecessorHead,List.filter_append,phiLetter,h] <;> omega
    · have hnot : ¬ a.1 ≤ 2 := by omega
      have hAllowed : (a.1 = 3 ∨ a.1 = 4) ∧ 3 ≤ a.2.1 ∧ a.2.1 ≤ D := by
        simpa only [LetterAllowed,if_neg hnot] using ha
      have hdne : a.2.1 ≠ 1 := by omega
      simp [rangeCount,rangeNodes,rangeRank,rangeInputWord,preimageWord,
        RangePhiFactorization.predecessorHead,List.filter_append,phiLetter,h,hdne] <;> omega
  · intro s hs hsmall
    omega

private theorem remove_two_equal_rank (D : Nat) (A B : Word) (a b : Letter) (r : Nat)
    (hEa : a.1 ≠ 4) (hEb : b.1 ≠ 4) (ha : rangeRank a = r) (hb : rangeRank b = r)
    (hr : 1 ≤ r) (hD : r ≤ rankBound D) :
    ChildDecrease D (A,B) (A++[a],B++[b]) := by
  apply decrease_of_rank D _ _ r
  · simp [counterCount,counterNodes,List.filter_append,hEa,hEb]
  · exact hr
  · exact hD
  · simp [rangeCount,rangeNodes,List.filter_append,ha,hb] <;> omega
  · intro s _hs hsmall
    have hne : r ≠ s := by omega
    simp [rangeCount,rangeNodes,List.filter_append,ha,hb,hne]

private theorem quadratic_decrease (D : Nat) (A B : Word) (j k a b : Int) :
    ChildDecrease D (A,B)
      (A++[quadraticLetter j,shiftLetter a],B++[quadraticLetter k,shiftLetter b]) := by
  apply decrease_shifted_heads
  apply remove_two_equal_rank D A B _ _ 2
  · simp [quadraticLetter]
  · simp [quadraticLetter]
  · simp [rangeRank,quadraticLetter]
  · simp [rangeRank,quadraticLetter]
  · omega
  · exact Nat.le_max_left 2 D

private theorem equal_rank_decrease (D : Nat) (A B : Word) (d c e : Nat)
    (j k a b : Int) (hd : 3 ≤ d) (hD : d ≤ D) :
    ChildDecrease D (A,B)
      (A++[kernelLetter d c j,shiftLetter a],B++[kernelLetter d e k,shiftLetter b]) := by
  apply decrease_shifted_heads
  apply remove_two_equal_rank D A B _ _ d
  · simp [kernelLetter]
  · simp [kernelLetter]
  · simp [rangeRank,kernelLetter]
  · simp [rangeRank,kernelLetter]
  · omega
  · exact hD.trans (Nat.le_max_right 2 D)

/-- This is the exact checked arbitrary-gap count identity, now connected to
strict histogram descent at the deleted lower rank, regardless of higher growth. -/
private theorem mixed_raw_decrease (D : Nat) (A B : Word) (n m c e : Nat)
    (j k : Int) (hD : n+m+3 ≤ D) :
    ChildDecrease D (retainedWord A n m c,B)
      (A++[kernelLetter (n+m+3) c j],B++[SourceRangeExpansion.lowerHead n e k]) := by
  have hv := MixedRangeWordGuardCompletion.Proof.mixedHeadDecrease A B n m c e j k
  apply decrease_of_rank D _ _ (n+2)
  · exact hv.1
  · omega
  · unfold rankBound
    omega
  · have h := hv.2 (n+2)
    simp only [eq_self_iff_true,if_true,lt_self_iff_false,false_and,if_false,Nat.add_zero] at h
    change rangeNodes (n+2) (retainedWord A n m c)+rangeNodes (n+2) B <
      rangeNodes (n+2) (A++[kernelLetter (n+m+3) c j])+
        rangeNodes (n+2) (B++[SourceRangeExpansion.lowerHead n e k])
    omega
  · intro s _hs hsmall
    have hne : s ≠ n+2 := by omega
    have hnot : ¬ (n+2<s ∧ s<n+m+3) := by omega
    have h := hv.2 s
    simpa only [rangeCount,if_neg hne,if_neg hnot,Nat.add_zero] using h

private theorem mixed_kernel_decrease (D : Nat) (A B : Word) (n m c e : Nat)
    (j k a b : Int) (hD : n+m+4 ≤ D) :
    ChildDecrease D (retainedWord A (n+1) m c,B)
      (A++[kernelLetter (n+m+4) c j,shiftLetter a],B++[kernelLetter (n+3) e k,shiftLetter b]) := by
  apply decrease_shifted_heads
  have h := mixed_raw_decrease D A B (n+1) m c e j k (by omega)
  have hhigh : n+1+m+3 = n+m+4 := by omega
  have hlow : n+1+2 = n+3 := by omega
  simpa [SourceRangeExpansion.lowerHead,hhigh,hlow] using h

private theorem mixed_quadratic_decrease (D : Nat) (A B : Word) (m c : Nat)
    (j k a b : Int) (hD : m+3 ≤ D) :
    ChildDecrease D (retainedWord A 0 m c,B)
      (A++[kernelLetter (m+3) c j,shiftLetter a],B++[quadraticLetter k,shiftLetter b]) := by
  apply decrease_shifted_heads
  have h := mixed_raw_decrease D A B 0 m c 0 j k (by omega)
  simpa [SourceRangeExpansion.lowerHead] using h

theorem actualGuardChildDecrease : Targets.ActualGuardChildDecrease := by
  intro D next current h
  induction h with
  | counterCounter A B n m c e j k _hn _hm =>
      exact counter_counter_decrease D A B n m c e j k
  | counterRange A B a n c j k _ha hr _hn =>
      exact counter_range_decrease D A B a n c j k hr
  | phiRange A B a j k ha hr =>
      exact phi_range_decrease D A B a j k ha hr
  | quadratic A B j k a b => exact quadratic_decrease D A B j k a b
  | equalRank A B d c e j k a b hd hD => exact equal_rank_decrease D A B d c e j k a b hd hD
  | mixedKernel A B n m c e j k a b hD => exact mixed_kernel_decrease D A B n m c e j k a b hD
  | mixedQuadratic A B m c j k a b hD => exact mixed_quadratic_decrease D A B m c j k a b hD
  | @swap next current _h ih =>
      unfold ChildDecrease
      rw [measure_swap,measure_swap]
      exact ih

theorem actualGuardChildWellFounded : Targets.ActualGuardChildWellFounded := by
  intro D
  apply Subrelation.wf (r := ChildDecrease D) ?_ (measureWellFounded D)
  intro next current h
  exact actualGuardChildDecrease D next current h

end LogicLineages.OrdinalComparison.GuardChildMeasureCompletion.Proof
