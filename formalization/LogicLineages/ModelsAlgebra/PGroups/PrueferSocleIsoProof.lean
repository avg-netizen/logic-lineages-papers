module
public import LogicLineages.ModelsAlgebra.PGroups.PrueferSocleIsoTargets
public import LogicLineages.ModelsAlgebra.PGroups.CyclicRoot
public import Mathlib.Tactic.FieldSimp
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary

theorem pruefer_socle_iso : Targets.prueferSocleIso := by
  classical
  intro p _
  have hpQ : (p:ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  let q : ℚ →+ RationalModIntegers := QuotientAddGroup.mk' _
  have ht : p • q (1/(p:ℚ)) = 0 := by
    rw [←map_nsmul]
    have he : p • (1/(p:ℚ)) = 1 := by
      rw [nsmul_eq_mul]
      field_simp
    rw [he]
    exact (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_zmultiples (1:ℚ))
  let t : PrueferModel p := ⟨q (1/(p:ℚ)),⟨1,by simpa using ht⟩⟩
  have hpt : p • t = 0 := Subtype.ext ht
  let f : ZMod p →+ PrueferModel p := cyclicRootHom p (PrueferModel p) t hpt
  have hf (a : ZMod p) : p • f a = 0 := by
    rw [←map_nsmul]
    have ha : p • a = 0 := by rw [nsmul_eq_mul,ZMod.natCast_self,zero_mul]
    rw [ha,map_zero]
  let g : ZMod p →+ pSocle p (⊤ : AddSubgroup (PrueferModel p)) :=
    f.codRestrict _ (fun a => ⟨AddSubgroup.mem_top _,hf a⟩)
  have hsur : Function.Surjective g := by
    intro x
    obtain ⟨r,hr⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1:ℚ))
      ((x:PrueferModel p):RationalModIntegers)
    have hz : q (p • r) = 0 := by
      rw [map_nsmul,hr]
      exact congrArg (fun z : PrueferModel p => (z:RationalModIntegers)) x.property.2
    obtain ⟨z,hz⟩ := AddSubgroup.mem_zmultiples_iff.mp ((QuotientAddGroup.eq_zero_iff _).mp hz)
    have he : (z:ℚ)/(p:ℚ) = r := by
      apply (div_eq_iff hpQ).mpr
      simpa only [zsmul_eq_mul,nsmul_eq_mul,mul_one,mul_comm] using hz
    refine ⟨(z:ZMod p),Subtype.ext ?_⟩
    change f (z:ZMod p) = (x:PrueferModel p)
    change cyclicRootHom p (PrueferModel p) t hpt (z:ZMod p) = _
    rw [cyclic_root_evaluation]
    apply Subtype.ext
    change z • q (1/(p:ℚ)) = ((x:PrueferModel p):RationalModIntegers)
    rw [←map_zsmul]
    simpa only [zsmul_eq_mul,mul_one_div,he] using hr
  have htne : t ≠ 0 := by
    intro he
    have hz : q (1/(p:ℚ)) = 0 := congrArg Subtype.val he
    obtain ⟨z,hz⟩ := AddSubgroup.mem_zmultiples_iff.mp ((QuotientAddGroup.eq_zero_iff _).mp hz)
    have hz' : (z:ℚ) = 1/(p:ℚ) := by simpa using hz
    have hh : (p:ℚ)*(z:ℚ) = 1 := by
      rw [hz']
      field_simp
    have hi : (p:ℤ)*z = 1 := by exact_mod_cast hh
    exact (Fact.out : p.Prime).not_dvd_one (Int.natCast_dvd_natCast.mp ⟨z,hi.symm⟩)
  have ho : addOrderOf t = p := by
    have hh := cyclic_root_order p (PrueferModel p) 0 t
      (by simpa only [zero_add,pow_one] using hpt)
      (by simpa only [pow_zero,one_nsmul] using htne)
    change addOrderOf t = p^(0+1) at hh
    simpa only [zero_add,pow_one] using hh
  have hi : Function.Injective f := by
    unfold f cyclicRootHom
    apply (ZMod.lift_injective p).mpr
    intro z hz
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mpr
    rw [←ho]
    exact (addOrderOf_dvd_iff_zsmul_eq_zero).mpr hz
  refine ⟨AddEquiv.ofBijective g ⟨?_,hsur⟩⟩
  intro x y h
  exact hi (congrArg Subtype.val h)
end LogicLineages.ModelsAlgebra.PGroups
