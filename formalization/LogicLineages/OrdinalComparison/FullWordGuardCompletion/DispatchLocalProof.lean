module
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.DispatchOrderProof
import LogicLineages.OrdinalComparison.FullWordGuardCompletion.ComparisonProof
import LogicLineages.OrdinalComparison.CounterWordGuardCompletion.WordProof
import LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion.WordProof
import LogicLineages.OrdinalComparison.ShiftedPhiRangeWordGuardCompletion.WordProof
import LogicLineages.OrdinalComparison.QuadraticWordGuardCompletion.WordProof
import LogicLineages.OrdinalComparison.ShiftedEqualRankWordGuardCompletion.WordProof
import LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.QuadraticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.FullWordGuardCompletion.DispatchLocalProof
open PolynomialGraphCompletion DispatchOrderProof
open CounterWordGuardCompletion CounterRangeWordGuardCompletion MixedRangeWordGuardCompletion

/-- A local proof retains all four literal words and both original inputs. -/
abbrev Result (L R U V : Word) (tie x y : Nat) : Prop :=
  WordDomain L x ∧ WordDomain R y ∧ WordDomain U x ∧ WordDomain V y ∧
    orderNat (wordValue L x) (wordValue R y) =
      liftTie tie (orderNat (wordValue U x) (wordValue V y))

theorem prefix_domain (A B : Word) (x : Nat)
    (h : WordDomain (A++B) x) : WordDomain A x := by
  induction A generalizing x with
  | nil => trivial
  | cons a A ih =>
      exact ⟨h.1, ih (letterValue a x) h.2⟩

theorem reverse_result (L R U V : Word) (tie x y : Nat)
    (htie : tie ≤ 2) (h : Result L R U V tie x y) :
    Result R L V U (reverseOrder tie) y x := by
  refine ⟨h.2.1, h.1, h.2.2.2.1, h.2.2.1, ?_⟩
  have hr := congrArg reverseOrder h.2.2.2.2
  rw [ComparisonProof.reverseOrder_orderNat,
    ComparisonProof.reverseOrder_liftTie tie
      (orderNat (wordValue U x) (wordValue V y)) htie
      (ComparisonProof.orderNat_bound _ _),
    ComparisonProof.reverseOrder_orderNat] at hr
  exact hr

theorem counterCounter (D : Nat) (A B : Word)
    (hA : WordAllowed D A) (hB : WordAllowed D B)
    (n m c e : Nat) (j k : Int) (hn : n+3 ≤ D) (hm : m+3 ≤ D) (x y : Nat)
    (hx : CounterWordGuardCompletion.guardTail A B n m c e j k ≤ x)
    (hy : CounterWordGuardCompletion.guardTail A B n m c e j k ≤ y) :
    Result (A++[counterLetter (n+3) c,shiftLetter j])
      (B++[counterLetter (m+3) e,shiftLetter k])
      (A++leaderWord n c) (B++leaderWord m e)
      (lexOrder (orderNat n m) (orderInt j k)) x y := by
  obtain ⟨hL,hR,_,_,hU,hV,hlt,heq,_⟩ :=
    CounterWordGuardCompletion.Proof.counterWordGuardCorrect
      D A B hA hB n m c e j k hn hm x y hx hy
  refine ⟨hL,hR,hU,hV,?_⟩
  apply comparison_of_lt_eq _ _ _ _ _
    (ComparisonProof.lexOrder_bound _ _
      (ComparisonProof.orderNat_bound _ _) (ComparisonProof.orderInt_bound _ _))
  · simpa only [CounterLexLT,lexOrder_eq_zero,ComparisonProof.orderNat_eq_zero,
      ComparisonProof.orderNat_eq_one,ComparisonProof.orderInt_eq_zero] using hlt
  · simpa only [lexOrder_eq_one,ComparisonProof.orderNat_eq_one,
      ComparisonProof.orderInt_eq_one] using heq

theorem counterRange (D : Nat) (A B : Word) (a : Letter)
    (hA : WordAllowed D A) (hB : WordAllowed D B) (ha : LetterAllowed D a)
    (hr : RangeHead a) (n c : Nat) (j k : Int) (hn : n+3 ≤ D) (x y : Nat)
    (hx : CounterRangeWordGuardCompletion.guardTail A B n c a j k ≤ x)
    (hy : CounterRangeWordGuardCompletion.guardTail A B n c a j k ≤ y) :
    Result (A++[counterLetter (n+3) c,shiftLetter j]) (B++[a,shiftLetter k])
      (A++leaderWord n c) (rangeInputWord B a) 0 x y := by
  obtain ⟨hL,hR,_,hU,_,hV,hlt,heq,_,_⟩ :=
    CounterRangeWordGuardCompletion.Proof.counterRangeWordGuardCorrect
      D A B a hA hB ha hr n c j k hn x y hx hy
  refine ⟨hL,hR,hU,hV,?_⟩
  apply comparison_of_lt_eq _ _ _ _ 0 (by omega)
  · simpa [le_iff_lt_or_eq] using hlt
  · simpa using heq

theorem phiRange (D : Nat) (A B : Word) (a : Letter)
    (hA : WordAllowed D A) (hB : WordAllowed D B) (ha : LetterAllowed D a)
    (hr : RangeHead a) (j k : Int) (x y : Nat)
    (hx : ShiftedPhiRangeWordGuardCompletion.guardTail A B a j k ≤ x)
    (hy : ShiftedPhiRangeWordGuardCompletion.guardTail A B a j k ≤ y) :
    Result (A++[phiLetter,shiftLetter j]) (B++[a,shiftLetter k])
      A (rangeInputWord B a) (orderInt j k) x y := by
  obtain ⟨hL,hR,_,hV,hlt,heq,_⟩ :=
    ShiftedPhiRangeWordGuardCompletion.Proof.phiRangeWordGuardCorrect
      D A B a hA hB ha hr j k x y hx hy
  refine ⟨hL,hR,prefix_domain A _ x hL,hV,?_⟩
  apply comparison_of_lt_eq _ _ _ _ _ (ComparisonProof.orderInt_bound _ _)
  · simpa only [ShiftedPhiRangeWordGuardCompletion.PreimageLexLT,
      ComparisonProof.orderInt_eq_zero] using hlt
  · simpa only [ComparisonProof.orderInt_eq_one] using heq

theorem quadratic (D : Nat) (A B : Word)
    (hA : WordAllowed D A) (hB : WordAllowed D B) (j k a b : Int) (x y : Nat)
    (hx : QuadraticWordGuardCompletion.guardTail A B j k a b ≤ x)
    (hy : QuadraticWordGuardCompletion.guardTail A B j k a b ≤ y) :
    Result (A++[quadraticLetter j,shiftLetter a])
      (B++[quadraticLetter k,shiftLetter b]) A B
      (lexOrder (orderInt j k) (orderInt a b)) x y := by
  obtain ⟨hL,hR,hlt,heq,_⟩ :=
    QuadraticWordGuardCompletion.Proof.quadraticWordGuardCorrect
      D A B hA hB j k a b x y hx hy
  refine ⟨hL,hR,prefix_domain A _ x hL,prefix_domain B _ y hR,?_⟩
  apply comparison_of_lt_eq _ _ _ _ _
    (ComparisonProof.lexOrder_bound _ _
      (ComparisonProof.orderInt_bound _ _) (ComparisonProof.orderInt_bound _ _))
  · simpa only [QuadraticWordGuardCompletion.ShiftLexLT,lexOrder_eq_zero,
      ComparisonProof.orderInt_eq_zero,ComparisonProof.orderInt_eq_one] using hlt
  · simpa only [lexOrder_eq_one,ComparisonProof.orderInt_eq_one] using heq

theorem equalRank (D : Nat) (A B : Word)
    (hA : WordAllowed D A) (hB : WordAllowed D B)
    (d c e : Nat) (j k a b : Int) (hd : 3 ≤ d) (hD : d ≤ D) (x y : Nat)
    (hx : ShiftedEqualRankWordGuardCompletion.guardTail A B d c e j k a b ≤ x)
    (hy : ShiftedEqualRankWordGuardCompletion.guardTail A B d c e j k a b ≤ y) :
    Result (A++[kernelLetter d c j,shiftLetter a])
      (B++[kernelLetter d e k,shiftLetter b]) A B
      (lexOrder (orderNat e c) (lexOrder (orderInt j k) (orderInt a b))) x y := by
  obtain ⟨hL,hR,hlt,heq,_⟩ :=
    ShiftedEqualRankWordGuardCompletion.Proof.shiftedEqualRankWordGuardCorrect
      D A B hA hB d c e j k a b hd hD x y hx hy
  have hec : (e = c) ↔ c = e := eq_comm
  refine ⟨hL,hR,prefix_domain A _ x hL,prefix_domain B _ y hR,?_⟩
  apply comparison_of_lt_eq _ _ _ _ _
    (ComparisonProof.lexOrder_bound _ _
      (ComparisonProof.orderNat_bound _ _)
      (ComparisonProof.lexOrder_bound _ _
        (ComparisonProof.orderInt_bound _ _) (ComparisonProof.orderInt_bound _ _)))
  · simpa only [ShiftedEqualRankWordGuardCompletion.KernelShiftLexLT,
      lexOrder_eq_zero,lexOrder_eq_one,ComparisonProof.orderNat_eq_zero,
      ComparisonProof.orderNat_eq_one,ComparisonProof.orderInt_eq_zero,
      ComparisonProof.orderInt_eq_one,hec] using hlt
  · simpa only [lexOrder_eq_one,ComparisonProof.orderNat_eq_one,
      ComparisonProof.orderInt_eq_one,hec] using heq

theorem mixedKernel (D : Nat) (A B : Word)
    (hA : WordAllowed D A) (hB : WordAllowed D B)
    (n m c e : Nat) (j k a b : Int) (hD : n+m+4 ≤ D) (x y : Nat)
    (hx : MixedRangeWordGuardCompletion.kernelGuardTail A B n m c e j k a b ≤ x)
    (hy : MixedRangeWordGuardCompletion.kernelGuardTail A B n m c e j k a b ≤ y) :
    Result (A++[kernelLetter (n+m+4) c j,shiftLetter a])
      (B++[kernelLetter (n+3) e k,shiftLetter b])
      (retainedWord A (n+1) m c) B
      (lexOrder (orderNat e c) (lexOrder (orderInt j k) (orderInt a b))) x y := by
  obtain ⟨hL,hR,_,hU,hlt,heq,_⟩ :=
    MixedRangeWordGuardCompletion.Proof.mixedKernelGuard
      D A B hA hB n m c e j k a b hD x y hx hy
  have hec : (e = c) ↔ c = e := eq_comm
  refine ⟨hL,hR,hU,prefix_domain B _ y hR,?_⟩
  apply comparison_of_lt_eq _ _ _ _ _
    (ComparisonProof.lexOrder_bound _ _
      (ComparisonProof.orderNat_bound _ _)
      (ComparisonProof.lexOrder_bound _ _
        (ComparisonProof.orderInt_bound _ _) (ComparisonProof.orderInt_bound _ _)))
  · simpa only [ShiftedEqualRankWordGuardCompletion.KernelShiftLexLT,
      lexOrder_eq_zero,lexOrder_eq_one,ComparisonProof.orderNat_eq_zero,
      ComparisonProof.orderNat_eq_one,ComparisonProof.orderInt_eq_zero,
      ComparisonProof.orderInt_eq_one,hec] using hlt
  · simpa only [lexOrder_eq_one,ComparisonProof.orderNat_eq_one,
      ComparisonProof.orderInt_eq_one,hec] using heq

theorem mixedQuadratic (D : Nat) (A B : Word)
    (hA : WordAllowed D A) (hB : WordAllowed D B)
    (m c : Nat) (j k a b : Int) (hD : m+3 ≤ D) (x y : Nat)
    (hx : MixedRangeWordGuardCompletion.quadraticGuardTail A B m c j k a b ≤ x)
    (hy : MixedRangeWordGuardCompletion.quadraticGuardTail A B m c j k a b ≤ y) :
    Result (A++[kernelLetter (m+3) c j,shiftLetter a])
      (B++[quadraticLetter k,shiftLetter b]) (retainedWord A 0 m c) B
      (lexOrder (orderInt (j-(((c+1)/2 : Nat) : Int)) k) (orderInt a b)) x y := by
  obtain ⟨hL,hR,_,hU,hlt,heq,_⟩ :=
    MixedRangeWordGuardCompletion.Proof.mixedQuadraticGuard
      D A B hA hB m c j k a b hD x y hx hy
  refine ⟨hL,hR,hU,prefix_domain B _ y hR,?_⟩
  apply comparison_of_lt_eq _ _ _ _ _
    (ComparisonProof.lexOrder_bound _ _
      (ComparisonProof.orderInt_bound _ _) (ComparisonProof.orderInt_bound _ _))
  · simpa only [QuadraticWordGuardCompletion.ShiftLexLT,lexOrder_eq_zero,
      ComparisonProof.orderInt_eq_zero,ComparisonProof.orderInt_eq_one] using hlt
  · simpa only [lexOrder_eq_one,ComparisonProof.orderInt_eq_one] using heq

end LogicLineages.OrdinalComparison.FullWordGuardCompletion.DispatchLocalProof
