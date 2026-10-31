module
public import LogicLineages.ModelsAlgebra.PGroups.HeadroomExtensionTargets
public import LogicLineages.ModelsAlgebra.PGroups.PrimeExtension
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteFiltration
public import LogicLineages.ModelsAlgebra.PGroups.ProperCoset
public import Mathlib.Data.Fintype.EquivFin
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v

theorem one_unit_headroom_extension : Targets.oneUnitHeadroomExtension.{u,v} := by
  intro G H _ _ p _ hG B C _ f δ α ρ hδα hαρ hpres hforward x hx hxα hcap hproper hpx hinf
  have hpxα : p • x ∈ (transfiniteFiltration p (α+1) : AddSubgroup G) := by
    rw [transfiniteFiltration_add_one]
    exact ⟨x,hxα,rfl⟩
  have hroot := hforward ⟨p • x,hpx⟩ (α+1) (add_le_add hαρ le_rfl) hpxα
  classical
  letI : Finite C := Finite.of_surjective f f.surjective
  letI := hinf
  rw [transfiniteFiltration_add_one] at hroot
  obtain ⟨y, hy, hpy⟩ := hroot
  have hav : ∃ s : pSocle p (transfiniteFiltration p α : AddSubgroup H), y + s ∉ C := by
    by_contra! hn
    let j : pSocle p (transfiniteFiltration p α : AddSubgroup H) → C :=
      fun s => ⟨y+s,hn s⟩
    apply not_injective_infinite_finite j
    intro a b hab
    apply Subtype.ext
    exact add_left_cancel (congrArg Subtype.val hab)
  obtain ⟨s, hs⟩ := hav
  let w : H := y+s
  have hwα : w ∈ (transfiniteFiltration p α : AddSubgroup H) :=
    (transfiniteFiltration p α).add_mem hy s.property.1
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
  have hrep (z : ↥(B ⊔ AddSubgroup.zmultiples x)) :
      ∃ (b : B) (k : ℤ), (z:G) = b + k • x ∧ F z = g b + k • w := by
    let S := B ⊔ AddSubgroup.zmultiples x
    let xS : S := ⟨x,(le_sup_right : AddSubgroup.zmultiples x ≤ S)
      (AddSubgroup.mem_zmultiples x)⟩
    obtain ⟨b,hb,t,ht,hbt⟩ := AddSubgroup.mem_sup.mp z.property
    obtain ⟨k,rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp ht
    let bB : B := ⟨b,hb⟩
    let bS : S := ⟨b,(le_sup_left : B ≤ S) hb⟩
    have hz : z = bS + k • xS := Subtype.ext hbt.symm
    refine ⟨bB,k,hbt.symm,?_⟩
    rw [hz,map_add,map_zsmul]
    change F bS + k • F xS = g bB + k • w
    rw [hFb bB,hFx]
  refine ⟨F,hF,hFb,?_,?_⟩
  · intro z β hβ
    obtain ⟨b,k,hco,hval⟩ := hrep z
    have cancel {K : Type u} [AddCommGroup K] (T : AddSubgroup K) (a b : K)
        (hb : b ∈ T) : a+b ∈ T ↔ a ∈ T := by
      constructor
      · intro h
        simpa using T.sub_mem h hb
      · intro h
        exact T.add_mem h hb
    rw [hval,hco]
    rw [cancel _ _ _ ((transfiniteFiltration p β).zsmul_mem
      (transfiniteFiltration_antitone p (hβ.trans hδα) hwα) k)]
    rw [cancel _ _ _ ((transfiniteFiltration p β).zsmul_mem
      (transfiniteFiltration_antitone p (hβ.trans hδα) hxα) k)]
    exact hpres b β hβ
  · intro z β hβ hzβ
    obtain ⟨b,k,hco,hval⟩ := hrep z
    by_cases hk : (p:ℤ) ∣ k
    · obtain ⟨j,hj⟩ := hk
      have hkmem : k • x ∈ B := by
        rw [hj,Int.mul_comm,mul_smul,natCast_zsmul]
        exact B.zsmul_mem hpx j
      have hzB : (z:G) ∈ B := by
        rw [hco]
        exact B.add_mem b.property hkmem
      have he : F z = g ⟨z,hzB⟩ := hFb ⟨z,hzB⟩
      rw [he]
      exact hforward ⟨z,hzB⟩ β (hβ.trans (Order.le_succ ρ)) hzβ
    · have hcop : Nat.Coprime k.natAbs p := by
        apply Nat.Coprime.symm
        apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
        intro h
        exact hk (Int.natCast_dvd.mpr h)
      have hm : k • x + (b:G) ∈ (transfiniteFiltration p β : AddSubgroup G) := by
        rw [hco] at hzβ
        simpa only [add_comm] using hzβ
      have hboth := (proper_coset_sum_membership G p hG B x hproper k hcop b β).mp hm
      have hβα : β ≤ α := by
        rcases hcap with hn | he
        · by_contra hnot
          exact hn (transfiniteFiltration_antitone p
            (Order.add_one_le_iff.mpr (lt_of_not_ge hnot)) hboth.1)
        · simpa only [he] using hβ
      rw [hval]
      exact (transfiniteFiltration p β).add_mem
        (hforward b β (hβ.trans (Order.le_succ ρ)) hboth.2)
        ((transfiniteFiltration p β).zsmul_mem
          (transfiniteFiltration_antitone p hβα hwα) k)

end LogicLineages.ModelsAlgebra.PGroups
