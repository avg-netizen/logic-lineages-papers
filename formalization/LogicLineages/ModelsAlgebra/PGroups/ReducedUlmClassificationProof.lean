module
public import LogicLineages.ModelsAlgebra.PGroups.ReducedUlmClassificationTargets
public import LogicLineages.ModelsAlgebra.PGroups.CountableUlmProof
public import LogicLineages.ModelsAlgebra.PGroups.CountableReducedZeroProof
public import LogicLineages.ModelsAlgebra.PGroups.UlmTransport
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

private theorem common_zero_cut (G H : Type) [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H] (p : ℕ) [Fact p.Prime]
    (hG : ∀ x : G, ∃ n : ℕ, p^n • x = 0) (hH : ∀ x : H, ∃ n : ℕ, p^n • x = 0)
    (hrG : IsReducedAddGroup G) (hrH : IsReducedAddGroup H) :
    ∃ δ : Ordinal.{0}, Order.IsSuccLimit δ ∧
      (transfiniteFiltration p δ : AddSubgroup G) = ⊥ ∧
      (transfiniteFiltration p δ : AddSubgroup H) = ⊥ := by
  obtain ⟨α,_,_,hα⟩ := countable_reduced_zero_limit G p hG hrG
  obtain ⟨β,_,hβlim,hβ⟩ := countable_reduced_zero_limit H p hH hrH
  refine ⟨α+β,Ordinal.isSuccLimit_add _ hβlim,?_,?_⟩
  · exact le_antisymm ((transfiniteFiltration_antitone p le_self_add).trans hα.le) bot_le
  · exact le_antisymm ((transfiniteFiltration_antitone p le_add_self).trans hβ.le) bot_le

theorem countable_reduced_ulm_finite_extension : Targets.countableReducedUlmFiniteExtension := by
  intro G H _ _ _ _ p _ hG hH hrG hrH hRank f
  obtain ⟨δ,hδ,hzG,hzH⟩ := common_zero_cut G H p hG hH hrG hrH
  exact countable_ulm_extends_at_zero_cut G H p hG hH δ hδ hzG hzH (fun α _ => hRank α) f

theorem countable_reduced_ulm_classification : Targets.countableReducedUlmClassification := by
  intro G H _ _ _ _ p _ hG hH hrG hrH
  constructor
  · rintro ⟨e⟩ α
    have hk : e.toAddMonoidHom.ker ≤ (transfiniteFiltration p α : AddSubgroup G) := by
      rw [e.toAddMonoidHom.ker_eq_bot e.injective]
      exact bot_le
    have hm := map_transfiniteFiltration_below p e.toAddMonoidHom e.surjective α hk α le_rfl
    have hu := GroupInfinitary.injective_ulm_isomorphism G H p
      (transfiniteFiltration p α) e.toAddMonoidHom e.injective
    rw [hm] at hu
    obtain ⟨u⟩ := hu
    exact u.rank_eq
  · intro hRank
    obtain ⟨δ,hδ,hzG,hzH⟩ := common_zero_cut G H p hG hH hrG hrH
    exact countable_ulm_at_zero_cut G H p hG hH δ hδ hzG hzH (fun α _ => hRank α)
end LogicLineages.ModelsAlgebra.PGroups
