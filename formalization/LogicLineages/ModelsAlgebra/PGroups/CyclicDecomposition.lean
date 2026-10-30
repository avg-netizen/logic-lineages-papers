module
public import LogicLineages.ModelsAlgebra.PGroups.CyclicDecompositionTargets
public import LogicLineages.ModelsAlgebra.PGroups.CyclicDirectSum
public import LogicLineages.ModelsAlgebra.PGroups.RootGeneration
public import LogicLineages.ModelsAlgebra.PGroups.UlmBasisLift
public import LogicLineages.ModelsAlgebra.PGroups.AdaptedSocle
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem cyclic_root_sum_injective : Targets.groupCyclicRootSumInjective := by
  intro p _ N I G _ y hy v hv hli
  apply bounded_socle_detects_injectivity p N (CyclicRootSum p N I) G
    (cyclicRootSumHom p N I G y hy) (cyclic_root_sum_exponent p N I)
  intro z hz hf
  obtain ⟨c,rfl⟩ := (cyclic_socle_coefficients_range p N I).ge hz
  have hc : Finsupp.linearCombination (ZMod p) v c = 0 := by
    apply Subtype.ext
    rw [← cyclic_root_sum_socle_composition p N I G y hy v hv c]
    exact hf
  have hc0 : c = 0 := hli.finsuppLinearCombination_injective (by simpa only [map_zero] using hc)
  rw [hc0, map_zero]

theorem cyclic_root_sum_surjective : Targets.groupCyclicRootSumSurjective := by
  classical
  intro p _ G _ N hb I b x y hy hx hroot
  let f := cyclicRootSumHom p N I G y hy
  have hr : AddSubgroup.closure (Set.range (fun a : Σ l : Fin N, I l => y a.1 a.2)) ≤ f.range := by
    apply (AddSubgroup.closure_le f.range).mpr
    rintro _ ⟨a,rfl⟩
    refine ⟨DFinsupp.single a 1, ?_⟩
    exact (cyclic_root_sum_single p N I G y hy a 1).trans
      (cyclic_root_generator (p ^ (a.1.val+1)) G (y a.1 a.2) (hy a.1 a.2))
  rw [ulm_roots_generate p G N hb I b x y hx hroot] at hr
  intro g
  exact hr (AddSubgroup.mem_top g)

theorem bounded_cyclic_decomposition : Targets.groupBoundedCyclicDecomposition := by
  classical
  intro p _ G _ N hb
  obtain ⟨I,b,x,y,h⟩ := ulm_basis_lift_existence p G
  let J : Fin N → Type := fun l => I l.val
  let yy : ∀ l : Fin N, J l → G := fun l => y l.val
  have hy : ∀ l i, p ^ (l.val+1) • yy l i = 0 := fun l i => (h l.val i).2.2
  let f := cyclicRootSumHom p N J G yy hy
  have hi : Function.Injective f := cyclic_root_sum_injective p N J G yy hy
    (includedSocleFamily p N J (fun l => x l.val))
    (fun a => (h a.1.val a.2).2.1)
    (adapted_socle_independent p G N J (fun l => b l.val) (fun l => x l.val)
      (fun l i => (h l.val i).1))
  have hs : Function.Surjective f := cyclic_root_sum_surjective p G N hb J
    (fun l => b l.val) (fun l => x l.val) yy hy
    (fun l i => (h l.val i).1) (fun l i => (h l.val i).2.1)
  exact ⟨J, ⟨(AddEquiv.ofBijective f ⟨hi,hs⟩).symm⟩⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
