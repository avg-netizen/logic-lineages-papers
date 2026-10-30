module
public import LogicLineages.ModelsAlgebra.PGroups.TerminalExactLengthTargets
public import LogicLineages.ModelsAlgebra.PGroups.FiniteOrdinalFiltration
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteTail
public import LogicLineages.ModelsAlgebra.PGroups.UlmFiniteIndependence
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v

theorem terminal_exact_length : Targets.groupTerminalExactLength.{u,v} := by
  intro G _ p δ N hN hbound hw
  let H := (transfiniteFiltration p δ : AddSubgroup G)
  have hzero : (transfiniteFiltration p (N : Ordinal.{v}) : AddSubgroup H) = ⊥ := by
    rw [finite_ordinal_filtration, GroupInfinitary.finite_filtration_multiple_image]
    apply AddSubgroup.ext
    intro x
    change (∃ y : H, p^N • y = x) ↔ x = 0
    constructor
    · rintro ⟨y,rfl⟩
      exact hbound y
    · intro hx
      exact ⟨0, by simp [hx]⟩
  have hzeroG : (transfiniteFiltration p (δ+(N : Ordinal.{v})) : AddSubgroup G) = ⊥ := by
    rw [← transfinite_tail_image, hzero, AddSubgroup.map_bot]
  refine ⟨hzeroG, ?_⟩
  obtain ⟨w,hw⟩ := hw
  have hlast : p^(N-1) • w ∈ (transfiniteFiltration p ((N-1 : ℕ) : Ordinal.{v}) : AddSubgroup H) := by
    rw [finite_ordinal_filtration, GroupInfinitary.finite_filtration_multiple_image]
    exact ⟨w,rfl⟩
  have hlastG := (transfinite_tail_membership G p δ ((N-1 : ℕ) : Ordinal.{v}) (p^(N-1) • w)).mp hlast
  have hcast : ((N-1 : ℕ) : Ordinal.{v}) + 1 = (N : Ordinal.{v}) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun n : ℕ => (n : Ordinal.{v})) (Nat.sub_add_cancel (Nat.succ_le_of_lt hN))
  intro α hα hbot
  have hα' : α ≤ δ + ((N-1 : ℕ) : Ordinal.{v}) := by
    apply Order.lt_add_one_iff.mp
    simpa only [add_assoc, hcast] using hα
  have hm := transfiniteFiltration_antitone p hα' hlastG
  exact hw (Subtype.ext (hbot.le hm))

end LogicLineages.ModelsAlgebra.PGroups
