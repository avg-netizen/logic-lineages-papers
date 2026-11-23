import LogicLineages.PersistentMarking.NativeTowerBandCoefficientModelProof
import LogicLineages.PersistentMarking.NativeTowerVariableDimensionBandImageRelIsoProof
import Mathlib.Order.RelIso.Basic

namespace LogicLineages.PersistentMarking.NativeTowerBandCoefficientRelIsoProof
open Spine NativeIteratorStrictTargets NativeTowerWitnessFamilyProof
open NativeTowerVariableDimensionBandsProof NativeTowerVariableDimensionBandImageRelIsoProof
open NativeTowerBandCoefficientModelProof

/-- An explicit two-way coefficient encoding; no choice of decoder. -/
def coefficientIso : BandLex ≃r coefficientStrict where
  toEquiv := ⟨toCoefficients,ofCoefficients,exact_OriginalBandCoefficientEncode,exact_OriginalBandCoefficientDecode⟩
  map_rel_iff' := fun {p q} => (exact_OriginalBandCoefficientStrictIff p q).symm

theorem exact_OriginalBandCoefficientRelIso :
    ∃ e : BandLex ≃r coefficientStrict,
      (∀ p, e p = toCoefficients p) ∧ (∀ q, e.symm q = ofCoefficients q) :=
  ⟨coefficientIso,fun _ => rfl,fun _ => rfl⟩

/-- The same actual closed native image is realized by the canonical
positive coefficient lists under length and dictionary comparison. -/
theorem exact_ActualFixedTowerCoefficientImage (S : Signature) (l : Nat) :
    ∃ e : coefficientStrict ≃r actualBandStrict S l,
      (∀ q, (e q).val = bandImage S l (ofCoefficients q)) ∧
      (∀ p : BandImage S l, NativeBelow p.val (closedTower S (l+2))) := by
  obtain ⟨physical,forward,bounded⟩ := exact_ActualFixedTowerBandRelIsoAndBound S l
  refine ⟨coefficientIso.symm.trans physical,?_,bounded⟩
  intro q
  exact forward (ofCoefficients q)

theorem exact_OriginalPositiveCoefficientWellOrder (S : Signature) (l : Nat) :
    IsWellOrder PositiveCoefficients coefficientStrict := by
  letI := exact_OriginalVariableBandLexWellOrder S l
  exact coefficientIso.symm.toRelEmbedding.isWellOrder

#print axioms exact_OriginalBandCoefficientRelIso
#print axioms exact_ActualFixedTowerCoefficientImage
#print axioms exact_OriginalPositiveCoefficientWellOrder

end LogicLineages.PersistentMarking.NativeTowerBandCoefficientRelIsoProof
