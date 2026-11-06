module
public import LogicLineages.OrdinalComparison.ShiftedEqualRankWordGuardCompletion.Targets
public import LogicLineages.OrdinalComparison.EqualRankWordGuardCompletion.KernelOrderProof
public import LogicLineages.OrdinalComparison.RangePhiFactorization.HeadProof
public import LogicLineages.OrdinalComparison.ShiftedPhiRangeWordGuardCompletion.ScalarProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ShiftedEqualRankWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion
open KernelSourceCompletion KernelSourceCompletion.UniformCompletion

/-- Remove one genuine coherent depth from both literal source kernels, use
accepted equal-rank order at those predecessors, then restore the outer shifts. -/
theorem shiftedKernelOrder : Targets.ShiftedKernelOrder := by
  intro d c e j k a b hd t u ht hu
  have hEqT : equalityTail d c e (j-1) (k-1) ≤ t := (Nat.le_max_left _ _).trans ht
  have hEqU : equalityTail d c e (j-1) (k-1) ≤ u := (Nat.le_max_left _ _).trans hu
  have hFT : RangePhiFactorization.factorTail (kernelLetter d c j) ≤ t :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans ht)
  have hFU : RangePhiFactorization.factorTail (kernelLetter d e k) ≤ u :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hu))
  have hST : ShiftedPhiRangeWordGuardCompletion.scalarTail a b ≤ t :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans ht))
  have hSU : ShiftedPhiRangeWordGuardCompletion.scalarTail a b ≤ u :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hu))
  have hAd : LetterAllowed d (kernelLetter d c j) := by
    simp [LetterAllowed,kernelLetter,hd]
  have hBd : LetterAllowed d (kernelLetter d e k) := by
    simp [LetterAllowed,kernelLetter,hd]
  have hL := RangePhiFactorization.Proof.headFactorization d (kernelLetter d c j) t hAd (Or.inr rfl) hFT
  have hR := RangePhiFactorization.Proof.headFactorization d (kernelLetter d e k) u hBd (Or.inr rfl) hFU
  have hFL : sourceSignedValue d c j t = Phi (sourceSignedValue d c (j-1) t) := hL.2.2
  have hFR : sourceSignedValue d e k u = Phi (sourceSignedValue d e (k-1) u) := hR.2.2
  have hLowerL : t ≤ sourceSignedValue d c (j-1) t :=
    iterate_self_le (fun z => (self_lt_Phi z).le) _ t
  have hLowerR : u ≤ sourceSignedValue d e (k-1) u :=
    iterate_self_le (fun z => (self_lt_Phi z).le) _ u
  have hOrder := EqualRankWordGuardCompletion.Proof.kernelOrderCorrect d c e (j-1) (k-1) hd t u hEqT hEqU
  have hEqual := (UniformCompletion.Proof.effectiveEqualityTail d c e (j-1) (k-1) hd t u hEqT hEqU).2.2.2.2
  have hCoreLT : sourceSignedValue d c (j-1) t < sourceSignedValue d e (k-1) u ↔
      EqualRankWordGuardCompletion.KernelLexLT c e j k t u := by
    rw [hOrder]
    unfold EqualRankWordGuardCompletion.KernelLexLT
    omega
  have hCoreEq : sourceSignedValue d c (j-1) t = sourceSignedValue d e (k-1) u ↔
      t = u ∧ c = e ∧ j = k := by
    constructor
    · intro h
      rcases hEqual.mp h with ⟨h1,h2,h3⟩
      exact ⟨h1,h2,by omega⟩
    · rintro ⟨rfl,rfl,rfl⟩
      rfl
  have hs := ShiftedPhiRangeWordGuardCompletion.Proof.shiftedPhiOrder a b
    (sourceSignedValue d c (j-1) t) (sourceSignedValue d e (k-1) u)
    (hST.trans hLowerL) (hSU.trans hLowerR)
  rw [←hFL,←hFR] at hs
  have hLex : ShiftedPhiRangeWordGuardCompletion.PreimageLexLT a b
      (sourceSignedValue d c (j-1) t) (sourceSignedValue d e (k-1) u) ↔
      KernelShiftLexLT c e j k a b t u := by
    unfold ShiftedPhiRangeWordGuardCompletion.PreimageLexLT
    rw [hCoreLT,hCoreEq]
    unfold EqualRankWordGuardCompletion.KernelLexLT KernelShiftLexLT
    simp only [and_or_left,and_assoc,or_assoc]
  refine ⟨hL.1,hR.1,hs.1,hs.2.1,?_,?_,?_⟩
  · exact hs.2.2.1.trans hLex
  · rw [hs.2.2.2.1,hCoreEq]
    simp only [and_assoc]
  · rw [hs.2.2.2.2,hLex,hCoreEq]
    simp only [and_assoc]

end LogicLineages.OrdinalComparison.ShiftedEqualRankWordGuardCompletion.Proof
