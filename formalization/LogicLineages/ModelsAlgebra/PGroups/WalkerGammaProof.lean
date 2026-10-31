module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerGammaTargets
public import LogicLineages.ModelsAlgebra.PGroups.WalkerConstructionProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem walker_countable_gamma_cut : Targets.walkerCountableGammaCut := by
  intro γ _
  apply Cardinal.mk_le_aleph0_iff.mp
  rw [Cardinal.mk_toType, walkerGammaCut, Ordinal.card_mul, Ordinal.card_omega0]
  have h : γ.card ≤ Cardinal.aleph0 := by
    simpa only [Cardinal.mk_toType] using (Cardinal.mk_le_aleph0 (α := γ.ToType))
  exact (mul_le_mul_left' h Cardinal.aleph0).trans_eq Cardinal.aleph0_mul_aleph0

private theorem infinite_of_infinite_ulm (p : ℕ) (G : Type) [AddCommGroup G]
    (α : Ordinal.{0})
    (hr : Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) = Cardinal.aleph0) :
    Infinite G := by
  apply not_finite_iff_infinite.mp
  intro hfin
  letI : Finite G := hfin
  letI : Finite (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) :=
    Finite.of_surjective _ (QuotientAddGroup.mk'_surjective (successorSocleSubgroup p (transfiniteFiltration p α : AddSubgroup G)))
  have h := (rank_le_card (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G))).trans_lt
    Cardinal.mk_lt_aleph0
  rw [hr] at h
  exact lt_irrefl _ h

theorem walker_gamma_source_construction : Targets.walkerGammaSourceConstruction := by
  intro p _ γ _ r hr
  let δ := walkerGammaCut γ
  letI : Countable δ.ToType := walker_countable_gamma_cut γ
  have hn := walker_construction_nature_length p δ r hr
  have ht := walker_source_families p δ r
  refine ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2,
    ht.2.2.1, ht.2.2.2.1, walker_family_ulm_table p δ r, ?_, ?_⟩
  · intro hγ
    have hδ : 0 < δ := mul_pos Ordinal.omega0_pos hγ
    have hrank := walker_family_ulm_table p δ r 0
    simp only [if_pos hδ] at hrank
    exact ⟨infinite_of_infinite_ulm p _ 0 hrank.1,
      infinite_of_infinite_ulm p _ 0 hrank.2⟩
  · intro s hs
    exact walker_construction_distinct p δ r s hs
end LogicLineages.ModelsAlgebra.PGroups
