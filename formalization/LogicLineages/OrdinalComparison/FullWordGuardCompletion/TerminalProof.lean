module
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.Targets
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.ComparisonProof
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.RunnerProof
public import LogicLineages.OrdinalComparison.OuterShiftNormalization.TerminalProof
public import LogicLineages.OrdinalComparison.CanonicalGuardSelector.BridgeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.FullWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion CanonicalGuardSelector
open GuardChildMeasureCompletion OuterShiftNormalization ComparisonProof

theorem core_empty_iff_shiftOnly (w : Word) : coreWord w = [] ↔ ShiftOnly w :=
  (OuterShiftNormalization.Proof.splitSyntax w).2.2.2

theorem nonlinear_of_core_nonempty (w : Word) (h : coreWord w ≠ []) :
    TerminalWordGrowthCompletion.Nonlinear w := by
  by_contra hn
  apply h
  apply (core_empty_iff_shiftOnly w).mpr
  intro a ha
  by_contra htag
  exact hn ⟨a,ha,htag⟩

theorem terminalRow_domain (p : WordPair) (x y : Nat) (hB : WordDomain p.2 y) :
    RowDomain (terminalRow p) (pairEnv x y) := by
  by_cases h : coreWord p.1 = []
  · simp [terminalRow,h,RowDomain,pairEnv,WordDomain,hB]
  · simp [terminalRow,h,RowDomain]

theorem terminalDomains (D : Nat) (p : WordPair) (hp : admitted D p = true)
    (x y : Nat) (hx : terminalTail p ≤ x) (hy : terminalTail p ≤ y) :
    WordDomain p.1 x ∧ WordDomain p.2 y ∧
      RowDomain (terminalRow p) (pairEnv x y) := by
  have ha := (RunnerProof.admissionCorrect D p).mp hp
  have hbase : leafPairTail p.1 p.2 ≤ terminalTail p := Nat.le_max_left _ _
  have hleft : wordTail p.1 ≤ terminalTail p :=
    (show wordTail p.1 ≤ leafPairTail p.1 p.2 from Nat.le_max_left _ _).trans hbase
  have hright : wordTail p.2 ≤ terminalTail p :=
    (show wordTail p.2 ≤ leafPairTail p.1 p.2 from Nat.le_max_right _ _).trans hbase
  have hA := (WordGuardCompletion.Proof.wordTailCorrect D p.1 x ha.1 (hleft.trans hx)).1
  have hB := (WordGuardCompletion.Proof.wordTailCorrect D p.2 y ha.2 (hright.trans hy)).1
  exact ⟨hA,hB,terminalRow_domain p x y hB⟩

theorem terminalSyntax : Targets.TerminalSyntax := by
  intro D p hp
  have hB := ((RunnerProof.admissionCorrect D p).mp hp).2
  by_cases hc : coreWord p.1 = []
  · constructor
    · intro a ha
      simp only [terminalRow,if_pos hc,List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl
      · intro b hb
        cases hb
      · exact hB
    · simp [terminalRow,hc,LinearInMaximum]
  · simp [terminalRow,hc,RowAllowed,LinearInMaximum]

theorem leafRowValue (p : WordPair) (h : coreWord p.1 = []) (x y : Nat) :
    RowValue (terminalRow p) (pairEnv x y) =
      (x : Int)+shiftSum p.1-(wordValue p.2 y : Int) := by
  simp [terminalRow,h,RowValue,pairEnv,wordValue]
  ring

theorem terminalComparison : Targets.TerminalComparison := by
  intro D p hp hstop x y hx hy hyx
  have ha := (RunnerProof.admissionCorrect D p).mp hp
  have hd := terminalDomains D p hp x y hx hy
  refine ⟨hd.1,hd.2.1,hd.2.2,?_⟩
  by_cases hA : coreWord p.1 = []
  · have hv := OuterShiftNormalization.Proof.shiftSumCorrect p.1 x
      ((core_empty_iff_shiftOnly p.1).mp hA) hd.1
    rw [orderNat_cast,hv,leafRowValue p hA x y]
    exact (orderInt_sub_zero _ _).symm
  · have hB : ShiftOnly p.2 :=
      ((CanonicalGuardSelector.Proof.selectionCoverage p.1 p.2).mp hstop).resolve_left
        (fun h => hA ((core_empty_iff_shiftOnly p.1).mpr h))
    have ht : nonlinearLeafTail p.1 p.2 ≤ terminalTail p := by
      simp only [terminalTail,if_neg hA]
      exact Nat.le_max_right _ _
    have hg := OuterShiftNormalization.Proof.nonlinearLeafGuard D p.1 p.2 x y ha.1
      (nonlinear_of_core_nonempty p.1 hA) hB (ht.trans hx) (ht.trans hy) hyx
    have ho := (orderNat_eq_two (wordValue p.1 x) (wordValue p.2 y)).mpr hg.2.2
    simpa [terminalRow,hA,RowValue,orderInt] using ho

theorem terminalSameVariable : Targets.TerminalSameVariable := by
  intro D p hp hstop x hx
  have ha := (RunnerProof.admissionCorrect D p).mp hp
  have hd := terminalDomains D p hp x x hx hx
  by_cases hA : coreWord p.1 = []
  · have hsA := (core_empty_iff_shiftOnly p.1).mp hA
    by_cases hB : coreWord p.2 = []
    · have hsB := (core_empty_iff_shiftOnly p.2).mp hB
      have hvA := OuterShiftNormalization.Proof.shiftSumCorrect p.1 x hsA hd.1
      have hvB := OuterShiftNormalization.Proof.shiftSumCorrect p.2 x hsB hd.2.1
      rw [orderNat_cast,hvA,hvB,terminalSame,if_pos hA,if_pos hB]
      exact orderInt_add_left _ _ _
    · have ht : nonlinearLeafTail p.2 p.1 ≤ terminalTail p := by
        simp only [terminalTail,if_pos hA,if_neg hB]
        exact Nat.le_max_right _ _
      have hg := OuterShiftNormalization.Proof.nonlinearLeafGuard D p.2 p.1 x x ha.2
        (nonlinear_of_core_nonempty p.2 hB) hsA (ht.trans hx) (ht.trans hx) (Nat.le_refl x)
      simpa only [terminalSame,if_pos hA,if_neg hB] using
        (orderNat_eq_zero (wordValue p.1 x) (wordValue p.2 x)).mpr hg.2.2
  · have hc := (terminalComparison D p hp hstop x x hx hx (Nat.le_refl x)).2.2.2
    simpa [terminalSame,terminalRow,hA,RowValue,orderInt] using hc

theorem terminalSame_bound (p : WordPair) : terminalSame p ≤ 2 := by
  unfold terminalSame
  split_ifs
  · exact orderInt_bound _ _
  · omega
  · omega

end LogicLineages.OrdinalComparison.FullWordGuardCompletion.Proof
