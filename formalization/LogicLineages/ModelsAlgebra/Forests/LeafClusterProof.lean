module

public import LogicLineages.ModelsAlgebra.Forests.LeafClusterTargets
public import LogicLineages.ModelsAlgebra.Forests.WidthFacts

/-! Saturation forces leaf bijections and cluster preservation for ordinary
order embeddings, without any root-, meet-, or leaf-preserving assumption. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.LeafClusterProof

theorem leafClustersLaminar : Targets.LeafClustersLaminar := by
  classical
  intro F u v
  by_cases huv : u ≤ v
  · exact Or.inr (Or.inl (fun _ h => le_trans huv h))
  by_cases hvu : v ≤ u
  · exact Or.inl (fun _ h => le_trans hvu h)
  right; right
  apply Set.disjoint_left.mpr
  intro ℓ hu hv
  rcases F.forest hu hv with h | h
  · exact huv h
  · exact hvu h

theorem saturatedLeafBijection : Targets.SaturatedLeafBijection := by
  classical
  intro F H e hcard
  let f : ForestLeaf F → ForestLeaf H := fun ℓ =>
    ⟨(exists_leaf_above (e ℓ.val)).choose, (exists_leaf_above (e ℓ.val)).choose_spec.2⟩
  have hf (ℓ : ForestLeaf F) : e ℓ.val ≤ (f ℓ).val :=
    (exists_leaf_above (e ℓ.val)).choose_spec.1
  have hinj : Function.Injective f := by
    intro a b hab
    have hb : e b.val ≤ (f a).val := by rw [hab]; exact hf b
    apply Subtype.ext
    rcases H.forest (hf a) hb with h | h
    · have h' := e.le_iff_le.mp h
      exact le_antisymm h' (a.property h')
    · have h' := e.le_iff_le.mp h
      exact le_antisymm (b.property h') h'
  have hcard' : Fintype.card (ForestLeaf H) ≤ Fintype.card (ForestLeaf F) := by
    simpa only [Fintype.card_subtype, leafFinset] using hcard
  have heq : Fintype.card (ForestLeaf F) = Fintype.card (ForestLeaf H) :=
    le_antisymm (Fintype.card_le_of_injective f hinj) hcard'
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, heq⟩
  exact ⟨Equiv.ofBijective f hbij, hf⟩

theorem saturatedClusterTransport : Targets.SaturatedClusterTransport := by
  intro F H e hcard
  obtain ⟨b, hb⟩ := saturatedLeafBijection F H e hcard
  refine ⟨b, hb, ?_⟩
  intro v ℓ
  constructor
  · intro hv
    rcases H.forest hv (hb ℓ) with h | h
    · exact e.le_iff_le.mp h
    · exact ℓ.property (e.le_iff_le.mp h)
  · intro hv
    exact le_trans (e.le_iff_le.mpr hv) (hb ℓ)

end LogicLineages.ModelsAlgebra.Forests.LeafClusterProof
