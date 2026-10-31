module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerUlmTargets
public import LogicLineages.ModelsAlgebra.PGroups.DirectSumUlmProof
public import LogicLineages.ModelsAlgebra.PGroups.WalkerReservoirProof
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteTailUlm
public import LogicLineages.ModelsAlgebra.PGroups.UlmEquivalenceTransport
public import LogicLineages.ModelsAlgebra.PGroups.CyclicUlm
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem walker_terminal_ulm_rank : Targets.walkerTerminalUlmRank := by
  intro p _ ξ _
  let H := (transfiniteFiltration p ξ : AddSubgroup (WalkerSourceGroup p ξ))
  obtain ⟨e⟩ := (walker_source_terminal p ξ).1
  have ht := transfinite_tail_ulm_rank (WalkerSourceGroup p ξ) p ξ 0
  change Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p 0 : AddSubgroup H)) =
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p (ξ+0) : AddSubgroup (WalkerSourceGroup p ξ))) at ht
  rw [transfiniteFiltration_zero, add_zero] at ht
  have he := GroupInfinitary.isomorphism_ulm_rank H (ZMod p) e p 0
  change Module.rank (ZMod p) (UlmLayer p (⊤ : AddSubgroup H)) =
    Module.rank (ZMod p) (UlmLayer p (⊤ : AddSubgroup (ZMod p))) at he
  have hc := GroupInfinitary.cyclic_ulm_rank p 1 0
  change Module.rank (ZMod p) (UlmLayer p (finiteFiltration p 0 : AddSubgroup (ZMod (p^1)))) =
    (if (0:ℕ)+1=1 then 1 else 0) at hc
  rw [pow_one] at hc
  simp only [finiteFiltration] at hc
  have hc' : Module.rank (ZMod p) (UlmLayer p (⊤ : AddSubgroup (ZMod p))) = 1 := by
    simp only [Nat.zero_add, ite_true] at hc
    exact hc
  exact ht.symm.trans (he.trans hc')

private theorem lower_countable (δ α : Ordinal.{0}) [Countable δ.ToType]
    (h : α ≤ δ) : Countable α.ToType := by
  apply Cardinal.mk_le_aleph0_iff.mp
  rw [Cardinal.mk_toType]
  apply (Ordinal.card_le_card h).trans
  simpa only [Cardinal.mk_toType] using (Cardinal.mk_le_aleph0 (α := δ.ToType))

theorem walker_reservoir_ulm_rank : Targets.walkerReservoirUlmRank := by
  classical
  intro p _ δ _ α
  letI : Countable (WalkerLowerReservoir p δ) := (walker_lower_reservoir p δ).1
  letI : Countable (UlmLayer p (transfiniteFiltration p α : AddSubgroup (WalkerLowerReservoir p δ))) :=
    (QuotientAddGroup.mk'_surjective (successorSocleSubgroup p (transfiniteFiltration p α : AddSubgroup (WalkerLowerReservoir p δ)))).countable
  by_cases hα : α < δ
  · rw [if_pos hα]
    apply le_antisymm
    · exact (rank_le_card (ZMod p) _).trans Cardinal.mk_le_aleph0
    · letI : Countable α.ToType := lower_countable δ α hα.le
      obtain ⟨i, hi⟩ := Ordinal.typein_surj (α := δ.ToType) (· < ·)
        (show α < Ordinal.type (α := δ.ToType) (· < ·) by simpa using hα)
      let F : δ.ToType × ℕ → Cardinal := fun j =>
        Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α :
          AddSubgroup (WalkerSourceGroup p (Ordinal.typein (α := δ.ToType) (· < ·) j.1))))
      have hf (n : ℕ) : F (i,n) = 1 := by
        dsimp only [F]
        rw [hi]
        exact walker_terminal_ulm_rank p α
      let a (n : ℕ) : (F (i,n)).out :=
        Classical.choice (Cardinal.nonempty_out (by rw [hf]; exact one_ne_zero))
      let f (n : ℕ) : Σ j, (F j).out := ⟨(i,n), a n⟩
      have hinj : Function.Injective f := by
        intro n m h
        exact congrArg (fun z : Σ j, (F j).out => z.1.2) h
      have hle := Cardinal.mk_le_of_injective hinj
      have hsum : Cardinal.aleph0 ≤ Cardinal.sum F := by
        simpa only [Cardinal.mk_nat, Cardinal.mk_sigma, Cardinal.mk_out] using hle
      rw [transfinite_direct_sum_ulm_rank]
      exact hsum
  · rw [if_neg hα]
    have hz : (transfiniteFiltration p α : AddSubgroup (WalkerLowerReservoir p δ)) = ⊥ :=
      le_antisymm ((transfiniteFiltration_antitone p (le_of_not_gt hα)).trans
        (walker_lower_reservoir p δ).2.2.1.le) bot_le
    apply (GroupInfinitary.ulm_rank_zero_socle p (WalkerLowerReservoir p δ) _).mpr
    intro x hx
    have hx0 := hx.1
    rw [hz] at hx0
    have he : x = 0 := hx0
    rw [he]
    exact (pStep p (transfiniteFiltration p α)).zero_mem
end LogicLineages.ModelsAlgebra.PGroups
