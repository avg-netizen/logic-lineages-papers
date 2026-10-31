module
public import LogicLineages.ModelsAlgebra.PGroups.HighRootExtensionTargets
public import LogicLineages.ModelsAlgebra.PGroups.PrimeExtension
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteFiltration
public import Mathlib.Data.Fintype.EquivFin
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v

theorem high_root_extension : Targets.highRootExtension.{u,v} := by
  intro G H _ _ p _ B C _ f δ hpres x hx hxδ hpx hroot hinf
  classical
  letI : Finite C := Finite.of_surjective f f.surjective
  letI := hinf
  rw [transfiniteFiltration_add_one] at hroot
  obtain ⟨y, hy, hpy⟩ := hroot
  have hav : ∃ s : pSocle p (transfiniteFiltration p δ : AddSubgroup H), y + s ∉ C := by
    by_contra! hn
    let j : pSocle p (transfiniteFiltration p δ : AddSubgroup H) → C :=
      fun s => ⟨y+s,hn s⟩
    apply not_injective_infinite_finite j
    intro a b hab
    apply Subtype.ext
    exact add_left_cancel (congrArg Subtype.val hab)
  obtain ⟨s, hs⟩ := hav
  let w : H := y+s
  have hwδ : w ∈ (transfiniteFiltration p δ : AddSubgroup H) :=
    (transfiniteFiltration p δ).add_mem hy s.property.1
  let g : B →+ H := C.subtype.comp f.toAddMonoidHom
  have hg : Function.Injective g := Subtype.val_injective.comp f.injective
  have hw : w ∉ g.range := by
    rintro ⟨b,hb⟩
    have hc : g b ∈ C := (f b).property
    rw [hb] at hc
    exact hs hc
  have hpw : p • w = g ⟨p • x,hpx⟩ := by
    change p • (y+(s:H)) = (f ⟨p • x,hpx⟩:H)
    have hps : p • (s:H) = 0 := s.property.2
    rw [nsmul_add, hps, add_zero]
    exact hpy
  obtain ⟨F,hF,hFb,hFx⟩ := prime_order_extension G H p B x hx hpx g hg w hw hpw
  refine ⟨F,hF,hFb,?_⟩
  intro z β hβ
  let S := B ⊔ AddSubgroup.zmultiples x
  let xS : S := ⟨x,(le_sup_right : AddSubgroup.zmultiples x ≤ S)
    (AddSubgroup.mem_zmultiples x)⟩
  obtain ⟨b,hb,t,ht,hbt⟩ := AddSubgroup.mem_sup.mp z.property
  obtain ⟨k,rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp ht
  let bB : B := ⟨b,hb⟩
  let bS : S := ⟨b,(le_sup_left : B ≤ S) hb⟩
  have hz : z = bS + k • xS := Subtype.ext hbt.symm
  have hval : F z = g bB + k • w := by
    rw [hz,map_add,map_zsmul]
    change F bS + k • F xS = g bB + k • w
    rw [hFb bB,hFx]
  have hco : (z:G) = b + k • x := hbt.symm
  have cancel {K : Type u} [AddCommGroup K] (T : AddSubgroup K) (a b : K)
      (hb : b ∈ T) : a+b ∈ T ↔ a ∈ T := by
    constructor
    · intro h
      simpa using T.sub_mem h hb
    · intro h
      exact T.add_mem h hb
  rw [hval,hco]
  rw [cancel _ _ _ ((transfiniteFiltration p β).zsmul_mem
    (transfiniteFiltration_antitone p hβ hwδ) k)]
  rw [cancel _ _ _ ((transfiniteFiltration p β).zsmul_mem
    (transfiniteFiltration_antitone p hβ hxδ) k)]
  exact hpres bB β hβ

end LogicLineages.ModelsAlgebra.PGroups
