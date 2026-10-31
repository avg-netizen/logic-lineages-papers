module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerReservoirTargets
public import LogicLineages.ModelsAlgebra.PGroups.WalkerGroupNatureProof
public import LogicLineages.ModelsAlgebra.PGroups.DirectSumFiltrationProof
public import Mathlib.Data.DFinsupp.Encodable
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

private theorem countable_lower_ordinal (δ ξ : Ordinal.{0}) [Countable δ.ToType]
    (h : ξ ≤ δ) : Countable ξ.ToType := by
  apply Cardinal.mk_le_aleph0_iff.mp
  rw [Cardinal.mk_toType]
  apply (Ordinal.card_le_card h).trans
  simpa only [Cardinal.mk_toType] using (Cardinal.mk_le_aleph0 (α := δ.ToType))

private theorem direct_sum_primary {ι : Type} {G : ι → Type}
    [∀ i, AddCommGroup (G i)] (p : ℕ)
    (h : ∀ i, ∀ x : G i, ∃ n : ℕ, p^n • x = 0) :
    ∀ x : DirectSum ι G, ∃ n : ℕ, p^n • x = 0 := by
  classical
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, by simp⟩
  | of i x =>
    obtain ⟨n, hn⟩ := h i x
    exact ⟨n, by rw [← map_nsmul, hn, map_zero]⟩
  | add x y hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n+m, ?_⟩
    rw [nsmul_add]
    have hnx : p^(n+m) • x = 0 := by
      rw [pow_add, mul_nsmul, hn, nsmul_zero]
    have hmy : p^(n+m) • y = 0 := by
      rw [pow_add, mul_comm, mul_nsmul, hm, nsmul_zero]
    rw [hnx, hmy, zero_add]

theorem walker_lower_reservoir : Targets.walkerLowerReservoir := by
  classical
  intro p _ δ _
  let ξ := fun i : δ.ToType × ℕ => Ordinal.typein (α := δ.ToType) (· < ·) i.1
  have hξ : ∀ i, ξ i < δ := fun i => by
    simpa only [ξ, Ordinal.type_toType] using Ordinal.typein_lt_type (α := δ.ToType) (· < ·) i.1
  letI (i : δ.ToType × ℕ) : Countable (ξ i).ToType :=
    countable_lower_ordinal δ (ξ i) (hξ i).le
  letI (i : δ.ToType × ℕ) : Countable (WalkerSourceGroup p (ξ i)) :=
    (walker_source_group_nature p (ξ i)).1
  have hz : (transfiniteFiltration p δ : AddSubgroup (WalkerLowerReservoir p δ)) = ⊥ := by
    rw [transfinite_direct_sum]
    apply le_antisymm
    · intro x hx
      change x = 0
      apply DirectSum.ext
      intro i
      have hi := (direct_sum_subgroup_coordinates _ x).mp hx i
      have hle : ξ i + 1 ≤ δ := Order.add_one_le_iff.mpr (hξ i)
      have hz := (transfiniteFiltration_antitone (G := WalkerSourceGroup p (ξ i)) p hle) hi
      dsimp only at hz
      rw [(walker_source_terminal p (ξ i)).2] at hz
      exact hz
    · exact bot_le
  refine ⟨?_, ?_, hz, ?_⟩
  · exact inferInstanceAs (Countable (Π₀ i : δ.ToType × ℕ, WalkerSourceGroup p (ξ i)))
  · exact direct_sum_primary p (fun i => (walker_source_group_nature p (ξ i)).2.1)
  · exact zero_stage_reduced (WalkerLowerReservoir p δ) p (Fact.out : p.Prime).ne_zero δ hz
end LogicLineages.ModelsAlgebra.PGroups
