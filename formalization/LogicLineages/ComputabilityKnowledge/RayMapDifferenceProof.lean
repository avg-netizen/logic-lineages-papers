module

public import LogicLineages.ComputabilityKnowledge.Comparators.RayMapDifference
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Direct subtraction of the existing source hereditary maps. All finite
sum identities are literal; eventual order/separation is not stipulated.
-/
namespace LogicLineages.ComputabilityKnowledge.RayMapDifferenceProof

open ExponentialNormalForm RayFiniteSum RayMapDifference

theorem literalAffineRay : Comparators.RayMapDifference.LiteralAffineRay := by
  intro d weights a t
  unfold affineValue raySlope
  rw [Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (Nat.mul_assoc _ _ _).symm

private theorem value_on_superset (d h : Nat) (f : Form d (h + 1))
    (s : Finset (Form d h)) (hs : f.support ⊆ s) (ρ : Fin d → Nat) :
    value (h + 1) f ρ = ∑ key ∈ s, affineValue (f key) ρ * 2 ^ value h key ρ := by
  change f.sum _ = _
  apply Finsupp.sum_of_support_subset f hs
  intro key _
  simp [affineValue]

theorem actualMapDifference : Comparators.RayMapDifference.ActualMapDifference := by
  intro d h f g weights t
  classical
  have hf : f.support ⊆ keySet f g := by
    intro key hk
    exact Finset.mem_union_left _ hk
  have hg : g.support ⊆ keySet f g := by
    intro key hk
    exact Finset.mem_union_right _ hk
  rw [value_on_superset d h f _ hf, value_on_superset d h g _ hg]
  simp only [Nat.cast_sum]
  rw [← Finset.sum_sub_distrib]
  unfold lowerSum
  apply Finset.sum_congr rfl
  intro key _
  rw [literalAffineRay d weights (f key) t, literalAffineRay d weights (g key) t]
  simp only [Nat.cast_mul, Nat.cast_add, slopeDifference, constantDifference]
  ring

theorem nontrivialSupport : Comparators.RayMapDifference.NontrivialSupport := by
  intro d h f g hne
  classical
  by_contra hnone
  apply hne
  apply Finsupp.ext
  intro key
  by_cases hk : key ∈ keySet f g
  · by_contra hnekey
    exact hnone ⟨key, hk, hnekey⟩
  · have hf : key ∉ f.support := fun hf => hk (Finset.mem_union_left _ hf)
    have hg : key ∉ g.support := fun hg => hk (Finset.mem_union_right _ hg)
    rw [Finsupp.notMem_support_iff.mp hf, Finsupp.notMem_support_iff.mp hg]

theorem equalCoefficientVanishes : Comparators.RayMapDifference.EqualCoefficientVanishes := by
  intro d h f g weights key heq
  simp only [slopeDifference, constantDifference, heq, sub_self, and_self]

theorem rayMapDifference : Comparators.RayMapDifference.Target :=
  ⟨literalAffineRay, actualMapDifference, nontrivialSupport, equalCoefficientVanishes⟩

end LogicLineages.ComputabilityKnowledge.RayMapDifferenceProof
