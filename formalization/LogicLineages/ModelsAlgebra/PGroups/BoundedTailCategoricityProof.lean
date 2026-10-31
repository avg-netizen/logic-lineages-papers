module
public import LogicLineages.ModelsAlgebra.PGroups.BoundedTailCategoricityTargets
public import LogicLineages.ModelsAlgebra.PGroups.CountableUlmProof
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteTailUlm
public import LogicLineages.ModelsAlgebra.PGroups.UlmFiniteIndependence
public import LogicLineages.ModelsAlgebra.PGroups.FiniteOrdinalFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

private theorem bounded_tail_zero (G : Type) [AddCommGroup G] (p : ℕ) (δ : Ordinal.{0}) (N : ℕ)
    (h : ∀ x : (transfiniteFiltration p δ : AddSubgroup G), p^N • x=0) :
    (transfiniteFiltration p (δ+Ordinal.omega0) : AddSubgroup G) = ⊥ := by
  let S : AddSubgroup G := transfiniteFiltration p δ
  have hz : (transfiniteFiltration p (N:Ordinal) : AddSubgroup S) = ⊥ := by
    rw [finite_ordinal_filtration,GroupInfinitary.finite_filtration_multiple_image]
    apply le_antisymm
    · rintro x ⟨y,rfl⟩; exact h y
    · exact bot_le
  have hstage : (transfiniteFiltration p (δ+N) : AddSubgroup G)=⊥ := by
    rw [← transfinite_tail_image,hz,AddSubgroup.map_bot]
  apply le_antisymm _ bot_le
  exact (transfiniteFiltration_antitone p (add_le_add le_rfl (Ordinal.nat_lt_omega0 N).le)).trans hstage.le

private theorem rank_invariant (p : ℕ) (G H : Type) [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (α : Ordinal.{0}) :
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) =
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H)) := by
  have hk : e.toAddMonoidHom.ker ≤ (transfiniteFiltration p α : AddSubgroup G) := by
    rw [e.toAddMonoidHom.ker_eq_bot e.injective]
    exact bot_le
  have hm := map_transfiniteFiltration_below p e.toAddMonoidHom e.surjective α hk α le_rfl
  have hu := GroupInfinitary.injective_ulm_isomorphism G H p
    (transfiniteFiltration p α) e.toAddMonoidHom e.injective
  rw [hm] at hu
  obtain ⟨u⟩ := hu
  exact u.rank_eq

theorem bounded_tail_categoricity : Targets.boundedTailCategoricity := by
  intro G H _ _ _ _ p _ hG hH δ N hN e hbelow
  have hNH : ∀ x : (transfiniteFiltration p δ : AddSubgroup H), p^N • x=0 := by
    intro x
    obtain ⟨y,rfl⟩ := e.surjective x
    rw [← map_nsmul,hN,map_zero]
  apply countable_ulm_at_zero_cut G H p hG hH (δ+Ordinal.omega0)
    (Ordinal.isSuccLimit_add _ Ordinal.isSuccLimit_omega0)
    (bounded_tail_zero G p δ N hN) (bounded_tail_zero H p δ N hNH)
  intro α _
  by_cases ha : α<δ
  · exact hbelow α ha
  · have he := rank_invariant p _ _ e (α-δ)
    rw [transfinite_tail_ulm_rank G p δ (α-δ),transfinite_tail_ulm_rank H p δ (α-δ),
      Ordinal.add_sub_cancel_of_le (le_of_not_gt ha)] at he
    exact he
end LogicLineages.ModelsAlgebra.PGroups
