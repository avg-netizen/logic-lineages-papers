import LogicLineages.PersistentMarking.NativeTowerBandFullCoefficientModelProof
import LogicLineages.PersistentMarking.NativeTowerBandCoefficientRelIsoProof

namespace LogicLineages.PersistentMarking.NativeTowerBandFullCoefficientRelIsoProof
open Spine NativeIteratorStrictTargets NativeTowerWitnessFamilyProof
open NativeTowerVariableDimensionBandsProof NativeTowerVariableDimensionBandImageRelIsoProof
open NativeTowerBandCoefficientModelProof NativeTowerBandCoefficientRelIsoProof
open NativeTowerBandFullCoefficientModelProof

def fullCoefficientIso : fullStrict ≃r coefficientStrict where
  toEquiv := ⟨raiseFull,lowerPositive,exact_FullCoefficientLeftInverse,exact_FullCoefficientRightInverse⟩
  map_rel_iff' := fun {x y} => (exact_FullCoefficientStrictIff x y).symm

theorem exact_OriginalFullFiniteCoefficientRelIso :
    ∃ e : fullStrict ≃r coefficientStrict,
      (∀ x, e x = raiseFull x) ∧ (∀ y, e.symm y = lowerPositive y) :=
  ⟨fullCoefficientIso,fun _ => rfl,fun _ => rfl⟩

/-- Adding zero does not enlarge, shrink, or move the actual native image.
The empty coefficient word is represented by the old first physical band
point, not by the original closed term Z. -/
theorem exact_ActualFixedTowerFullCoefficientImage (S : Signature) (l : Nat) :
    ∃ e : fullStrict ≃r actualBandStrict S l,
      (∀ q, (e q).val = bandImage S l (ofCoefficients (raiseFull q))) ∧
      (e ⟨[],True.intro⟩).val = bandImage S l ⟨0,(0 : Nat)⟩ ∧
      (∀ p : BandImage S l, NativeBelow p.val (closedTower S (l+2))) := by
  obtain ⟨physical,forward,bounded⟩ := exact_ActualFixedTowerCoefficientImage S l
  have actual : ∀ q : FullCoefficients,
      ((fullCoefficientIso.trans physical) q).val = bandImage S l (ofCoefficients (raiseFull q)) :=
    fun q => forward (raiseFull q)
  refine ⟨fullCoefficientIso.trans physical,actual,?_,bounded⟩
  exact actual ⟨[],True.intro⟩

theorem exact_OriginalFullCoefficientWellOrder (S : Signature) (l : Nat) :
    IsWellOrder FullCoefficients fullStrict := by
  letI := exact_OriginalPositiveCoefficientWellOrder S l
  exact fullCoefficientIso.toRelEmbedding.isWellOrder

#print axioms exact_OriginalFullFiniteCoefficientRelIso
#print axioms exact_ActualFixedTowerFullCoefficientImage
#print axioms exact_OriginalFullCoefficientWellOrder

end LogicLineages.PersistentMarking.NativeTowerBandFullCoefficientRelIsoProof
