module

public import LogicLineages.ModelsAlgebra.PGroups.FullShiftTargets
public import LogicLineages.ModelsAlgebra.PGroups.BlockShift
public import LogicLineages.ModelsAlgebra.PGroups.UpperCyclic

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem full_shift_injective : Targets.groupFullShiftInjective := by
  intro p _ k t ℓ h s r x y he
  apply Prod.ext
  · exact block_shift_injective p k t ℓ h (congrArg Prod.fst he)
  · simpa [fullShiftHom] using congrArg (fun z : FullShiftGroup p k t ℓ s r => z.2) he

theorem full_shift_socle_roots : Targets.groupFullShiftSocleRoots := by
  intro p _ k t ℓ h s r hk hr x hx
  obtain ⟨y, hy⟩ := block_shift_socle_roots p k t hk ℓ h x.1 (congrArg Prod.fst hx)
  obtain ⟨z, hz⟩ := upper_cyclic_socle_roots p k s hk r hr x.2 (congrArg Prod.snd hx)
  exact ⟨(y, z), Prod.ext hy hz⟩

theorem full_short_no_root : Targets.groupFullShortNoRoot := by
  intro p _ k t ℓ s r j hj hk
  have hw := block_short_no_root p k t ℓ j hj hk
  constructor
  · apply Prod.ext
    · exact hw.1
    · simp [fullShortWitness]
  · rintro ⟨y, hy⟩
    exact hw.2 ⟨y.1, congrArg Prod.fst hy⟩

theorem full_shift_exponent : Targets.groupFullShiftExponent := by
  intro p k t ℓ h s r x
  let N := fullExponentBound k s r
  have hk : k ≤ N := le_max_left _ _
  have hr (a : Fin s) : r a ≤ N :=
    (Finset.le_sup (Finset.mem_univ a)).trans (le_max_right _ _)
  apply Prod.ext
  · apply Prod.ext
    · funext j
      exact power_cyclic_annihilation p (ℓ j) N ((h j).trans hk) (x.1.1 j)
    · apply Finsupp.ext
      intro i
      exact power_cyclic_annihilation p k N hk (x.1.2 i)
  · exact upper_cyclic_annihilation p s N r hr x.2

theorem full_shift_countable : Targets.groupFullShiftCountable := by
  intro p _ k t ℓ s r
  letI : Countable (BlockShiftGroup p k t ℓ) := block_shift_countable p k t ℓ
  letI : Finite (UpperCyclicGroup p s r) := upper_cyclic_finite p s r
  infer_instance

theorem full_shift_infinite : Targets.groupFullShiftInfinite := by
  intro p _ k t ℓ s r hk
  letI : Infinite (BlockShiftGroup p k t ℓ) := block_shift_infinite p k t ℓ hk
  infer_instance

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
