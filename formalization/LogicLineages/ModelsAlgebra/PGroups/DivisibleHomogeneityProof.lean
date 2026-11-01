module
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleHomogeneityTargets
public import LogicLineages.ModelsAlgebra.PGroups.CompatibleHomProof
public import LogicLineages.ModelsAlgebra.PGroups.PrimarySocleControlProof
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary

theorem primary_divisible_socle_detects_automorphism :
    Targets.primaryDivisibleSocleDetectsAutomorphism := by
  intro D _ p _ hprimary hdiv F hF
  constructor
  · apply primary_socle_injectivity p D D hprimary F
    intro x y h
    apply hF.1
    exact Subtype.ext h
  · apply primary_divisible_socle_surjectivity p D D (Fact.out:p.Prime).ne_zero hprimary hdiv F
    intro x
    obtain ⟨y,hy⟩ := hF.2 x
    exact ⟨y,congrArg Subtype.val hy⟩

theorem primary_divisible_finite_homogeneity : Targets.primaryDivisibleFiniteHomogeneity := by
  classical
  intro D _ _ p _ hprimary hdiv B C _ f
  let V : AddSubgroup D := pSocle p ⊤
  let W : Submodule (ZMod p) V := AddSubgroup.toZModSubmodule p (B.comap V.subtype)
  let W' : Submodule (ZMod p) V := AddSubgroup.toZModSubmodule p (C.comap V.subtype)
  let eW : W ≃+ W' :=
    { toFun := fun x => by
        let b : B := ⟨((x:V):D),x.property⟩
        have hpx : p • ((x:V):D)=0 := (x:V).property.2
        have hb : p • b=0 := Subtype.ext hpx
        refine ⟨⟨(f b:D),AddSubgroup.mem_top _,?_⟩,(f b).property⟩
        change p • (f b:D)=0
        exact congrArg (fun z:C=>(z:D)) (by rw [←map_nsmul,hb,map_zero] : p • f b=0)
      invFun := fun x => by
        let c : C := ⟨((x:V):D),x.property⟩
        have hpx : p • ((x:V):D)=0 := (x:V).property.2
        have hc : p • c=0 := Subtype.ext hpx
        refine ⟨⟨(f.symm c:D),AddSubgroup.mem_top _,?_⟩,(f.symm c).property⟩
        change p • (f.symm c:D)=0
        exact congrArg (fun z:B=>(z:D)) (by rw [←map_nsmul,hc,map_zero] : p • f.symm c=0)
      left_inv := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z:B=>(z:D)) (f.symm_apply_apply ⟨((x:V):D),x.property⟩)
      right_inv := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z:C=>(z:D)) (f.apply_symm_apply ⟨((x:V):D),x.property⟩)
      map_add' := fun x y => by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z:C=>(z:D))
          (f.map_add ⟨((x:V):D),x.property⟩ ⟨((y:V):D),y.property⟩) }
  let eL : W ≃ₗ[ZMod p] W' :=
    LinearEquiv.ofBijective (eW.toAddMonoidHom.toZModLinearMap p) eW.bijective
  let j : W → B := fun x=>⟨((x:V):D),x.property⟩
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z:B=>(z:D)) h
  letI : Finite W := Finite.of_injective j hj
  letI : Module.Finite (ZMod p) W := Module.Finite.of_finite
  obtain ⟨g,hg⟩ := Submodule.exists_linearEquiv_restrict_eq eL
  let fD : B →+ D := C.subtype.comp f.toAddMonoidHom
  let u : V →+ D := V.subtype.comp g.toAddEquiv.toAddMonoidHom
  have hcompatible : ∀ (x:D) (hB:x∈B) (hV:x∈V), fD ⟨x,hB⟩=u ⟨x,hV⟩ := by
    intro x hxB hxV
    let w : W := ⟨⟨x,hxV⟩,hxB⟩
    have hh : (eL w:V)=g (w:V) := hg w
    exact congrArg (fun z:V=>(z:D)) hh
  obtain ⟨F,hFB,hFV⟩ := compatible_divisible_hom_extension D D hdiv B V fD u hcompatible
  have hs : socleEndomorphism D p F=g.toAddEquiv.toAddMonoidHom := by
    ext x
    exact hFV x
  have hbij : Function.Bijective (socleEndomorphism D p F) := by
    rw [hs]
    exact g.bijective
  have hF := primary_divisible_socle_detects_automorphism D p hprimary hdiv F hbij
  exact ⟨AddEquiv.ofBijective F hF,hFB⟩

end LogicLineages.ModelsAlgebra.PGroups
