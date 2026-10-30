module
public import LogicLineages.ModelsAlgebra.PGroups.CyclicDirectSumTargets
public import LogicLineages.ModelsAlgebra.PGroups.CyclicSocleCoordinates
public import Mathlib.Data.Finsupp.Ext
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem cyclic_root_sum_single : Targets.groupCyclicRootSumSingle := by
  classical
  intro p N I G _ y hy a z
  exact DFinsupp.sumAddHom_single
    (fun a : Σ l : Fin N, I l => cyclicRootHom (p ^ (a.1.val+1)) G (y a.1 a.2) (hy a.1 a.2)) a z

theorem cyclic_root_sum_exponent : Targets.groupCyclicRootSumExponent := by
  intro p N I z
  ext a
  exact power_cyclic_annihilation p (a.1.val+1) N (Nat.succ_le_of_lt a.1.isLt) (z a)

theorem cyclic_socle_coefficients_injective : Targets.groupCyclicSocleCoefficientsInjective := by
  intro p _ N I c d h
  ext a
  exact cyclic_socle_coordinate_injective p a.1.val (congrArg (fun z => z a) h)

theorem cyclic_socle_coefficients_range : Targets.groupCyclicSocleCoefficientsRange := by
  classical
  intro p _ N I
  ext z
  constructor
  · rintro ⟨c,rfl⟩
    change p • cyclicSocleCoefficients p N I c = 0
    ext a
    exact (cyclic_socle_coordinate_range p a.1.val).le ⟨c a,rfl⟩
  · intro hz
    have hcoord : ∀ a : Σ l : Fin N, I l, ∃ c : ZMod p, cyclicSocleCoordinate p a.1.val c = z a := by
      intro a
      apply (cyclic_socle_coordinate_range p a.1.val).ge
      exact congrArg (fun w => w a) hz
    choose c hc using hcoord
    have hs : ∀ a, c a ≠ 0 → a ∈ z.support := by
      intro a ha
      apply DFinsupp.mem_support_iff.mpr
      intro hz0
      apply ha
      apply cyclic_socle_coordinate_injective p a.1.val
      rw [hc, hz0, map_zero]
    let d : (Σ l : Fin N, I l) →₀ ZMod p := Finsupp.onFinset z.support c hs
    refine ⟨d, ?_⟩
    ext a
    exact hc a

theorem cyclic_root_sum_socle_composition : Targets.groupCyclicRootSumSocleComposition := by
  classical
  intro p _ N I G _ y hy v hv
  let f := (cyclicRootSumHom p N I G y hy).comp (cyclicSocleCoefficients p N I)
  let g := (pSocle p (⊤ : AddSubgroup G)).subtype.comp
    (Finsupp.linearCombination (ZMod p) v).toAddMonoidHom
  have hfg : f = g := by
    apply Finsupp.addHom_ext
    intro a c
    change cyclicRootSumHom p N I G y hy (cyclicSocleCoefficients p N I (Finsupp.single a c)) =
      ((Finsupp.linearCombination (ZMod p) v (Finsupp.single a c) : pSocle p (⊤ : AddSubgroup G)) : G)
    have hs : cyclicSocleCoefficients p N I (Finsupp.single a c) =
        DFinsupp.single a (cyclicSocleCoordinate p a.1.val c) := by
      simp only [cyclicSocleCoefficients, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        Finsupp.toDFinsupp_single, DFinsupp.mapRange_single]
    rw [hs, cyclic_root_sum_single, cyclic_socle_root_composition, hv,
      Finsupp.linearCombination_single]
    have hc : c • v a = c.val • v a := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
    rw [hc]
    rfl
  intro c
  exact DFunLike.congr_fun hfg c

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
