import LogicLineages.PersistentMarking.NativeTowerVariableDimensionBandReflectionProof
import Mathlib.Logic.Equiv.Set
import Mathlib.Order.RelIso.Basic

namespace LogicLineages.PersistentMarking.NativeTowerVariableDimensionBandImageRelIsoProof
open Spine NativeIteratorStrictTargets NativeTowerWitnessFamilyProof
open NativeTowerVariableDimensionBandsProof NativeTowerVariableDimensionBandReflectionProof

/-- The actual image of the whole dependent sum, within one fixed native tower. -/
abbrev BandImage (S : Signature) (l : Nat) := ↥(Set.range (bandImage S l))

def actualBandStrict (S : Signature) (l : Nat) : BandImage S l → BandImage S l → Prop :=
  fun a b => NativeBelow a.val b.val

noncomputable def actualBandRelIso (S : Signature) (l : Nat) :
    BandLex ≃r actualBandStrict S l where
  toEquiv := Equiv.ofInjective (bandImage S l)
    (fun {_ _} eq => exact_OriginalBandImageInjective S l _ _ eq)
  map_rel_iff' := by
    intro p q
    change NativeBelow (bandImage S l p) (bandImage S l q) ↔ BandLex p q
    exact exact_OriginalBandNativeComparisonIff S l p q

theorem exact_OriginalVariableBandLexWellOrder (S : Signature) (l : Nat) :
    IsWellOrder BandCoords BandLex where
  wf := exact_OriginalBandLexWellFounded S l
  trichotomous := fun p q notEarlier notLater =>
    ((exact_OriginalBandLexTrichotomy p q).resolve_left notEarlier).resolve_right notLater

theorem exact_ActualFixedTowerBandRelIsoAndBound (S : Signature) (l : Nat) :
    ∃ e : BandLex ≃r actualBandStrict S l,
      (∀ p, (e p).val = bandImage S l p) ∧
      (∀ p : BandImage S l, NativeBelow p.val (closedTower S (l+2))) := by
  refine ⟨actualBandRelIso S l,fun _ => rfl,?_⟩
  rintro ⟨value,⟨p,rfl⟩⟩
  exact (exact_OriginalTowerVariableDimensionLexSum S l).1 p

theorem exact_ActualFixedTowerBandImageWellOrder (S : Signature) (l : Nat) :
    IsWellOrder (BandImage S l) (actualBandStrict S l) := by
  letI := exact_OriginalVariableBandLexWellOrder S l
  exact (actualBandRelIso S l).symm.toRelEmbedding.isWellOrder

#print axioms exact_OriginalVariableBandLexWellOrder
#print axioms exact_ActualFixedTowerBandRelIsoAndBound
#print axioms exact_ActualFixedTowerBandImageWellOrder

end LogicLineages.PersistentMarking.NativeTowerVariableDimensionBandImageRelIsoProof
