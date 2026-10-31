module
public import LogicLineages.ModelsAlgebra.PGroups.PrueferFiniteSocleTargets
public import LogicLineages.ModelsAlgebra.PGroups.CyclicRoot
public import Mathlib.Tactic.FieldSimp
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary

theorem pruefer_finite_socle : Targets.prueferFiniteSocle := by
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
  let g : ZMod p → pSocle p (⊤ : AddSubgroup (PrueferModel p)) :=
    fun a => ⟨f a,AddSubgroup.mem_top _,hf a⟩
  apply Finite.of_surjective g
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

theorem finite_pruefer_power_socle : Targets.finitePrueferPowerSocle := by
  intro p _ n
  letI := pruefer_finite_socle p
  let j : pSocle p (⊤ : AddSubgroup (Fin n → PrueferModel p)) →
      (Fin n → pSocle p (⊤ : AddSubgroup (PrueferModel p))) :=
    fun x i => ⟨x.val i,AddSubgroup.mem_top _,congrFun x.property.2 i⟩
  apply Finite.of_injective j
  intro x y h
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (congrFun h i)
end LogicLineages.ModelsAlgebra.PGroups
