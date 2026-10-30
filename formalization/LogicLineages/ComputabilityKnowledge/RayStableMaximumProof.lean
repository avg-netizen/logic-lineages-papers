module

public import LogicLineages.ComputabilityKnowledge.Comparators.RayStableMaximum

@[expose] public section

/-! Finite greatest-key selection from proved pairwise lower-height gaps.
The selection uses a single positive threshold evaluation to orient all
future comparisons. No eventual-order oracle or final ray theorem is assumed.
-/
namespace LogicLineages.ComputabilityKnowledge.RayStableMaximumProof

open RayStableMaximum

theorem stableGreatestKey : Comparators.RayStableMaximum.StableGreatestKey := by
  intro ι s v N hs hgap
  classical
  obtain ⟨greatest, hg, hmax⟩ := s.exists_max_image (fun a => v a (max N 1)) hs
  refine ⟨greatest, hg, ?_⟩
  intro a ha hne t ht
  rcases hgap a ha greatest hg hne with hab | hba
  · exact hab t ((le_max_left _ _).trans ht)
  · have hrev := hba (max N 1) (le_max_left _ _)
    have hless := hmax a ha
    have hpos : 1 ≤ max N 1 := le_max_right _ _
    omega

theorem uniqueGreatestKey : Comparators.RayStableMaximum.UniqueGreatestKey := by
  intro ι s v T a b hpos ha hb
  by_contra hne
  have hab := hb.2 a ha.1 hne T le_rfl
  have hba := ha.2 b hb.1 (Ne.symm hne) T le_rfl
  omega

theorem zeroGreatestCase : Comparators.RayStableMaximum.ZeroGreatestCase := by
  intro ι s v T zero hpos hz hg a ha
  by_contra hne
  have h := hg.2 a ha hne T le_rfl
  rw [hz] at h
  omega

theorem rayStableMaximum : Comparators.RayStableMaximum.Target :=
  ⟨stableGreatestKey, uniqueGreatestKey, zeroGreatestCase⟩

end LogicLineages.ComputabilityKnowledge.RayStableMaximumProof
