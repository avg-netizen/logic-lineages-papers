module
public import LogicLineages.OrdinalComparison.GuardChildMeasureCompletion.MeasureProof
public import LogicLineages.OrdinalComparison.OuterShiftNormalization.SyntaxProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.GuardChildMeasureCompletion.Proof
open PolynomialGraphCompletion CounterWordGuardCompletion AdjacentRangeWordGuardCompletion

/-- Reversing orientation preserves each literal occurrence total. -/
theorem measure_swap (D : Nat) (p : WordPair) :
    wordMeasure D (p.2,p.1) = wordMeasure D p := by
  apply measure_ext D
  · simp [counterCount,Nat.add_comm]
  · intro r _ _
    simp [rangeCount,Nat.add_comm]

/-- Outer shifts contribute neither counters nor positive range ranks, even
when the preceding words contain arbitrary malformed letters. -/
theorem measure_shifts (D : Nat) (A B : Word) (j k : Int) :
    wordMeasure D (A++[shiftLetter j],B++[shiftLetter k]) = wordMeasure D (A,B) := by
  apply measure_ext D
  · simp [counterCount,counterNodes,List.filter_append,shiftLetter]
  · intro r hr _
    have h0 : (0 : Nat) ≠ r := by omega
    simp [rangeCount,rangeNodes,List.filter_append,rangeRank,shiftLetter,h0]

/-- The established source normalization preserves all measured occurrences. -/
theorem measure_normalized (D : Nat) (A B : Word)
    (hA : WordAllowed D A) (hB : WordAllowed D B) :
    wordMeasure D (OuterShiftNormalization.normalizedWord A,
      OuterShiftNormalization.normalizedWord B) = wordMeasure D (A,B) := by
  have hNA := OuterShiftNormalization.Proof.normalizationSyntax D A hA
  have hNB := OuterShiftNormalization.Proof.normalizationSyntax D B hB
  apply measure_ext D
  · exact congrArg₂ Nat.add hNA.2.2.2.1 hNB.2.2.2.1
  · intro r hr _
    cases r with
    | zero => omega
    | succ r =>
        exact congrArg₂ Nat.add (hNA.2.2.2.2 r) (hNB.2.2.2.2 r)

theorem measureInvariance : Targets.MeasureInvariance :=
  ⟨measure_swap,measure_shifts,measure_normalized⟩

/-- The finite histogram includes Phi and V even below degree two, and the
original admission bound covers every genuine kernel degree. -/
theorem admissionRankBound : Targets.AdmissionRankBound := by
  intro D w hw a ha
  have hAllowed := hw a ha
  have hTwo : 2 ≤ rankBound D := Nat.le_max_left 2 D
  have hD : D ≤ rankBound D := Nat.le_max_right 2 D
  by_cases h1 : a.1 = 1
  · have hOne : 1 ≤ rankBound D := by omega
    simpa [rangeRank,h1] using hOne
  by_cases h2 : a.1 = 2
  · simpa [rangeRank,h1,h2] using hTwo
  by_cases h3 : a.1 = 3
  · have hLarge : ¬ a.1 ≤ 2 := by omega
    simp only [LetterAllowed,if_neg hLarge] at hAllowed
    have hBound : a.2.1 ≤ rankBound D := Nat.le_trans hAllowed.2.2 hD
    simpa [rangeRank,h1,h2,h3] using hBound
  · simp [rangeRank,h1,h2,h3]

end LogicLineages.OrdinalComparison.GuardChildMeasureCompletion.Proof
