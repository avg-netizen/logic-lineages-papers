module
public import LogicLineages.ModelsAlgebra.PGroups.IntrinsicBoundedScottTargets
public import LogicLineages.ModelsAlgebra.PGroups.DescriptorScott
public import Mathlib.SetTheory.Cardinal.ToNat
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

private theorem filtration_bot_of_bound (G : Type) [AddCommGroup G] (p N : ℕ)
    (h : ∀ g : G, p ^ N • g = 0) : finiteFiltration p N = (⊥ : AddSubgroup G) := by
  apply le_antisymm _ bot_le
  intro g hg
  obtain ⟨x,rfl⟩ := (finite_filtration_multiple_image G p N).le hg
  exact h x

theorem intrinsic_bounded_difference_scott : Targets.groupIntrinsicBoundedDifferenceScott := by
  classical
  intro p _ G _ _ k N hk hkN hb hf hi hr
  letI : Finite (multipleImage G (p ^ k)) := hf
  letI : Fintype (multipleImage G (p ^ k)) := Fintype.ofFinite _
  let a : Fin (k-1) → ℕ := fun j =>
    (Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j.val : AddSubgroup G))).toNat
  refine ⟨boundedDescriptor (multipleImage G (p ^ k)) p k N a, ?_⟩
  apply bounded_descriptor_scott p (multipleImage G (p ^ k)) k N hk hkN a G
    ⟨AddEquiv.refl _⟩ (Set.infinite_coe_iff.mp hi) (filtration_bot_of_bound G p N hb)
  intro j
  exact (Cardinal.cast_toNat_of_lt_aleph0 (hr j.val j.isLt)).symm

theorem intrinsic_bounded_pi_scott : Targets.groupIntrinsicBoundedPiScott := by
  classical
  intro p _ G _ _ k N hk hkN hb hf hi hr
  letI : Finite (multipleImage G (p ^ k)) := hf
  letI : Fintype (multipleImage G (p ^ k)) := Fintype.ofFinite _
  refine ⟨zeroLowerDescriptor (multipleImage G (p ^ k)) p k N, ?_⟩
  exact zero_lower_descriptor_scott p (multipleImage G (p ^ k)) k N hk hkN G
    ⟨AddEquiv.refl _⟩ (Set.infinite_coe_iff.mp hi) (filtration_bot_of_bound G p N hb) hr

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
