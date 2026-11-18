module
public import LogicLineages.CartierObserverCurrent.GeometricStateTargets
public import LogicLineages.CartierObserverCurrent.CanonicalExtensionProof
public import LogicLineages.CartierObserverCurrent.RootInterpolationProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.GeometricState
open SplittingRoots RootInterpolation Polynomial

private theorem mapped_roots (d : Nat) [DecidableEq (Closure d)] :
    ((rootProduct d).map (algebraMap (FieldAt d) (Closure d))).roots =
      ((SplittingRoots.rootSet d).image (algebraMap (FieldAt d) (Closure d))).val := by
  classical
  simp only [rootProduct, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [← Finset.prod_image (algebraMap (FieldAt d) (Closure d)).injective.injOn]
  exact roots_prod_X_sub_C _

private theorem denominator_geometry (d : Nat) (f : RatFunc (FieldAt d)) :
    f.denom ∣ rootProduct d ↔ supportedSimple d f := by
  classical
  let σ := algebraMap (FieldAt d) (Closure d)
  let Q := f.denom.map σ
  let T := (rootProduct d).map σ
  let S := (SplittingRoots.rootSet d).image σ
  have hQ : Q ≠ 0 := Polynomial.map_ne_zero f.denom_ne_zero
  have hT : T ≠ 0 := Polynomial.map_ne_zero (productDegree d).1.ne_zero
  have hr : T.roots = S.val := mapped_roots d
  have hdiv : f.denom ∣ rootProduct d ↔ Q.roots ≤ S.val := by
    rw [← Polynomial.map_dvd_map σ σ.injective f.monic_denom]
    change Q ∣ T ↔ _
    rw [(IsAlgClosed.splits Q).dvd_iff_roots_le_roots hQ hT, hr]
  have hc : Q.roots ≤ S.val ↔
      (∀ z : Closure d, 0 < Q.rootMultiplicity z → z ∈ S) ∧
      (∀ z : Closure d, Q.rootMultiplicity z ≤ 1) := by
    constructor
    · intro h
      constructor
      · intro z hz
        apply Multiset.subset_of_le h
        exact Multiset.count_pos.mp (by simpa only [count_roots] using hz)
      · intro z
        rw [← count_roots]
        exact (Multiset.count_le_of_le z h).trans (Multiset.nodup_iff_count_le_one.mp S.nodup z)
    · rintro ⟨hs, hm⟩
      apply Multiset.le_iff_count.mpr
      intro z
      by_cases hz : z ∈ Q.roots
      · have hp : 0 < Q.rootMultiplicity z := by
          simpa only [count_roots] using (Multiset.count_pos.mpr hz)
        rw [Multiset.count_eq_one_of_mem S.nodup (hs z hp), count_roots]
        exact hm z
      · rw [Multiset.count_eq_zero_of_notMem hz]
        exact Nat.zero_le _
  rw [hdiv, hc]
  have he : (geometricExtension d f).denom = Q :=
    CanonicalExtension.denominatorMap _ _ σ f
  change ((∀ z, 0 < Q.rootMultiplicity z → z ∈ S) ∧ _) ↔
    ((∀ z, 0 < (geometricExtension d f).denom.rootMultiplicity z →
      ∃ a : Root d, σ a.val = z) ∧
      (∀ z, (geometricExtension d f).denom.rootMultiplicity z ≤ 1))
  rw [he]
  apply and_congr _ Iff.rfl
  constructor
  · intro h z hz
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp (h z hz)
    exact ⟨⟨a, ha⟩, he⟩
  · intro h z hz
    obtain ⟨a, he⟩ := h z hz
    exact Finset.mem_image.mpr ⟨a.val, a.property, he⟩

theorem actualStateEquivalence : Targets.ActualStateEquivalence := by
  intro d f
  exact and_congr Iff.rfl (denominator_geometry d f)

theorem actualBaseEquivalence : Targets.ActualBaseEquivalence := by
  intro d g
  exact and_congr Iff.rfl (denominator_geometry d (ProfileDescent.extend d g))

#audit_namespace LogicLineages.CartierObserverCurrent.GeometricState
end LogicLineages.CartierObserverCurrent.GeometricState
