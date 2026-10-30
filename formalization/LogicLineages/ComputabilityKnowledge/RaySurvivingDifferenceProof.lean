module

public import LogicLineages.ComputabilityKnowledge.Comparators.RaySurvivingDifference
public import LogicLineages.ComputabilityKnowledge.RayMapDifferenceProof

@[expose] public section

/-! Zero coefficient deletion and lower-height hypotheses for the original
hereditary maps. No unproved normalization or eventual-order supplier is used.
-/
namespace LogicLineages.ComputabilityKnowledge.RaySurvivingDifferenceProof

open ExponentialNormalForm RayMapDifference RayFiniteSum RaySurvivingDifference

theorem exactSurvivingSupport : Comparators.RaySurvivingDifference.ExactSurvivingSupport := by
  intro d h f g key
  classical
  simp only [survivingKeys, Finset.mem_filter]

theorem nonemptySurvivingSupport : Comparators.RaySurvivingDifference.NonemptySurvivingSupport := by
  intro d h f g
  constructor
  · rintro ⟨key, hk⟩ heq
    have hd := (exactSurvivingSupport d h f g key).mp hk
    exact hd.2 (by rw [heq])
  · intro hne
    obtain ⟨key, hk, hd⟩ := RayMapDifferenceProof.nontrivialSupport d h f g hne
    exact ⟨key, (exactSurvivingSupport d h f g key).mpr ⟨hk, hd⟩⟩

theorem actualSurvivingSum : Comparators.RaySurvivingDifference.ActualSurvivingSum := by
  intro d h f g weights t
  classical
  rw [RayMapDifferenceProof.actualMapDifference d h f g weights t]
  unfold lowerSum
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro key hk hnot
  have heq : f key = g key := by
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨hk, hne⟩)
  have hz := RayMapDifferenceProof.equalCoefficientVanishes d h f g weights key heq
  rw [hz.1, hz.2]
  simp

theorem actualLowerKeys : Comparators.RaySurvivingDifference.ActualLowerKeys := by
  intro d h f g hf hg key hk
  classical
  have hmem := ((exactSurvivingSupport d h f g key).mp hk).1
  change key ∈ f.support ∪ g.support at hmem
  rcases Finset.mem_union.mp hmem with hmem | hmem
  · exact hf key hmem
  · exact hg key hmem

theorem raySurvivingDifference : Comparators.RaySurvivingDifference.Target :=
  ⟨exactSurvivingSupport, nonemptySurvivingSupport, actualSurvivingSum, actualLowerKeys⟩

end LogicLineages.ComputabilityKnowledge.RaySurvivingDifferenceProof
