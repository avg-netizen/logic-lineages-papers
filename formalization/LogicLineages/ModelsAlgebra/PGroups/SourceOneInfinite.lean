module
public import LogicLineages.ModelsAlgebra.PGroups.SourceOneInfiniteTargets
public import LogicLineages.ModelsAlgebra.PGroups.OneInfiniteBounds
public import LogicLineages.ModelsAlgebra.PGroups.FiniteTail
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

private theorem source_images (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G]
    (k N : ℕ) (hk : 0 < k) (hkN : k ≤ N) (hb : ∀ g : G, p ^ N • g = 0)
    (hm : Module.rank (ZMod p) (UlmLayer p (finiteFiltration p (k-1) : AddSubgroup G)) = Cardinal.aleph0)
    (ho : ∀ j : ℕ, j < N → j ≠ k-1 →
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) < Cardinal.aleph0) :
    Finite (multipleImage G (p ^ k)) ∧ Infinite (multipleImage G (p ^ (k-1))) := by
  have hf := finite_tail_from_ranks p G N hb k hkN (fun j hkj hjN => ho j hjN (by omega))
  have hi := infinite_ulm_infinite_filtration p G (k-1) hm
  rw [finite_filtration_multiple_image G p k] at hf
  rw [finite_filtration_multiple_image G p (k-1)] at hi
  exact ⟨hf,hi⟩

theorem source_positive_lower_scott_bounds : Targets.groupSourcePositiveLowerScottBounds := by
  intro p _ G _ _ k N hk hkN hb hm ho hn
  obtain ⟨hf,hi⟩ := source_images p G k N hk hkN hb hm ho
  apply positive_lower_scott_bounds p G k N hk hkN hb hf hi _ hn
  intro j hj
  exact ho j (by omega) (by omega)

theorem source_zero_lower_scott_bounds : Targets.groupSourceZeroLowerScottBounds := by
  intro p _ G _ _ k N hk hkN hb hm ho hz
  obtain ⟨hf,hi⟩ := source_images p G k N hk hkN hb hm ho
  exact zero_lower_scott_bounds p G k N hk hkN hb hf hi hz

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
