module
public import LogicLineages.PermittedControl.ThresholdTargets
public import LogicLineages.PermittedControl.OutputOffsetProof
public import LogicLineages.PermittedControl.EqualGapCertificateCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem signedComparisonCode_correct (a b : Nat) :
    signedComparisonCode a b=integerComparison (signedOffsetValue a) (signedOffsetValue b) := by
  by_cases ha : a%2=0 <;> by_cases hb : b%2=0 <;>
    simp only [signedComparisonCode,signedOffsetValue,ha,hb,↓reduceIte,integerComparison,numericalComparison] <;>
    split_ifs <;> omega

 theorem signedTranslateCode_correct (c x : Nat) :
    signedTranslateCode c x=((x:Int)+signedOffsetValue c).toNat := by
  by_cases hc : c%2=0 <;>
    simp only [signedTranslateCode,signedOffsetValue,hc,↓reduceIte] <;> omega

 theorem signedOffsetMagnitudeCode_correct (c : Nat) :
    signedOffsetMagnitudeCode c=(signedOffsetValue c).natAbs := (signed_offset_abs c).symm

 theorem reverseComparisonCode_correct (a b : Nat) :
    reverseComparisonCode (numericalComparison a b)=numericalComparison b a := by
  simp only [reverseComparisonCode,numericalComparison]
  split_ifs <;> omega

 theorem inverseTableDecisionCode_correct (sign y h E F : Nat) (hs : sign≤2) (hh : 0<h)
    (hr : InverseTableRows sign y h F E) : inverseTableDecisionCode sign y h=numericalComparison E F := by
  rcases (show sign=0 ∨ sign=1 ∨ sign=2 by omega) with hz | ho | ht
  · have hr' := hr.2.2 hz
    simp only [inverseTableDecisionCode,hz,show ¬(0:Nat)=1 by omega,show ¬(0:Nat)=2 by omega,↓reduceIte,numericalComparison]
    split_ifs <;> omega
  · have hr' := hr.1 ho
    simp only [inverseTableDecisionCode,ho,↓reduceIte,numericalComparison]
    split_ifs <;> omega
  · have hr' := hr.2.1 ht
    simp only [inverseTableDecisionCode,ht,show ¬(2:Nat)=1 by omega,↓reduceIte,numericalComparison]
    split_ifs <;> omega

 theorem integerComparison_nat (a b : Nat) : integerComparison (a:Int) (b:Int)=numericalComparison a b := by
  simp only [integerComparison,numericalComparison,Int.natCast_lt,Int.natCast_inj]

 theorem translated_input_margin (p : IntervalPairCodes) (s : SignedShiftCodes) (B x y : Nat)
    (hx : translatedThresholdTailCode p s B≤x) (hy : translatedThresholdTailCode p s B≤y) :
    0≤(x:Int)+signedOffsetValue s.1.1 ∧ 0≤(y:Int)+signedOffsetValue s.1.2 ∧
    thresholdTailCode p B≤signedTranslateCode s.1.1 x ∧
    thresholdTailCode p B≤signedTranslateCode s.1.2 y ∧
    (signedOffsetValue s.2.1).natAbs+(signedOffsetValue s.2.2).natAbs+2≤
      min (signedTranslateCode s.1.1 x) (signedTranslateCode s.1.2 y) := by
  unfold translatedThresholdTailCode at hx hy
  simp only [signedOffsetMagnitudeCode_correct] at hx hy
  have hr : -(signedOffsetValue s.1.1)≤((signedOffsetValue s.1.1).natAbs:Int) :=
    by simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -signedOffsetValue s.1.1))
  have hs : -(signedOffsetValue s.1.2)≤((signedOffsetValue s.1.2).natAbs:Int) :=
    by simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -signedOffsetValue s.1.2))
  rw [signedTranslateCode_correct,signedTranslateCode_correct]
  omega

end LogicLineages.PermittedControl
