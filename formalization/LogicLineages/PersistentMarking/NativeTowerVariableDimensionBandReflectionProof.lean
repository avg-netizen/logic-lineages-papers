import LogicLineages.PersistentMarking.NativeTowerVariableDimensionBandsProof
import LogicLineages.PersistentMarking.NativeTowerNestedInnerOrbitReflectionProof

namespace LogicLineages.PersistentMarking.NativeTowerVariableDimensionBandReflectionProof
open Spine NativeIteratorStrictTargets NativeIndexedCarrierTargets
open NativeTowerOuterIndexConeProof NativeTowerNestedInnerOrbitReflectionProof
open NativeTowerVariableDimensionBandsProof

theorem exact_OriginalBandLexTrichotomy (p q : BandCoords) :
    BandLex p q ∨ p = q ∨ BandLex q p := by
  rcases p with ⟨d,p⟩
  rcases q with ⟨e,q⟩
  rcases Nat.lt_trichotomy d e with earlier | eq | later
  · exact Or.inl (Or.inl earlier)
  · subst e
    rcases exact_OriginalOrbitLexTrichotomy d p q with first | same | last
    · exact Or.inl (Or.inr ⟨rfl,first⟩)
    · subst q
      exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr ⟨rfl,last⟩))
  · exact Or.inr (Or.inr (Or.inl later))

theorem exact_OriginalBandNativeComparisonIff (S : Signature) (l : Nat) (p q : BandCoords) :
    NativeBelow (bandImage S l p) (bandImage S l q) ↔ BandLex p q := by
  refine ⟨?_,exact_OriginalTowerBandLexPreservation S l p q⟩
  intro edge
  rcases exact_OriginalBandLexTrichotomy p q with earlier | eq | later
  · exact earlier
  · rw [eq] at edge
    exact False.elim (exact_OriginalNativeStrictNoLoop S _ edge)
  · have reverse := exact_OriginalTowerBandLexPreservation S l q p later
    exact False.elim (exact_OriginalNativeStrictNoLoop S _ (transBase edge reverse))

theorem exact_OriginalBandImageInjective (S : Signature) (l : Nat) :
    ∀ p q, bandImage S l p = bandImage S l q → p = q := by
  intro p q eq
  rcases exact_OriginalBandLexTrichotomy p q with earlier | same | later
  · have edge := exact_OriginalTowerBandLexPreservation S l p q earlier
    rw [eq] at edge
    exact False.elim (exact_OriginalNativeStrictNoLoop S _ edge)
  · exact same
  · have edge := exact_OriginalTowerBandLexPreservation S l q p later
    rw [eq] at edge
    exact False.elim (exact_OriginalNativeStrictNoLoop S _ edge)

/-- No ordinal representation or arithmetic instance: just comparison into
the checked well-founded original native relation. -/
theorem exact_OriginalBandLexWellFounded (S : Signature) (l : Nat) : WellFounded BandLex := by
  have nativeWF := NativeClosedStrictWellFoundedChecks.exact_ClosedNativeStrictWellFounded S indexType
  have inverseWF := InvImage.wf (bandImage S l) nativeWF
  apply Subrelation.wf _ inverseWF
  intro p q smaller
  exact exact_OriginalTowerBandLexPreservation S l p q smaller

#print axioms exact_OriginalBandLexTrichotomy
#print axioms exact_OriginalBandNativeComparisonIff
#print axioms exact_OriginalBandImageInjective
#print axioms exact_OriginalBandLexWellFounded

end LogicLineages.PersistentMarking.NativeTowerVariableDimensionBandReflectionProof
