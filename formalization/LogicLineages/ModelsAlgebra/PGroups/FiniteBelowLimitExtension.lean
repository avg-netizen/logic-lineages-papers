module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteBelowLimitExtensionTargets
public import LogicLineages.ModelsAlgebra.PGroups.BelowLimitExtension
public import Mathlib.SetTheory.Cardinal.Finite
public meta import Lean.Elab.Tactic.Omega
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v

theorem finite_below_limit_extension : Targets.groupFiniteBelowLimitExtension.{u,v} := by
  classical
  intro G H _ _ p _ hG hH D _ B C f δ hδ hBD hcut hpres hRank
  let Result (B : AddSubgroup G) (C : AddSubgroup H) (f : B ≃+ C) (hBD : B ≤ D) : Prop :=
    ∃ F : D →+ H, Function.Injective F ∧
      (∀ b : B, F ⟨b,hBD b.property⟩ = (f b:H)) ∧
      ∀ (y : D) (β : Ordinal.{v}), β ≤ δ →
        (F y ∈ (transfiniteFiltration p β : AddSubgroup H) ↔
          (y:G) ∈ (transfiniteFiltration p β : AddSubgroup G))
  have main : ∀ n : ℕ, ∀ (B : AddSubgroup G) (C : AddSubgroup H) (f : B ≃+ C) (hBD : B ≤ D),
      Nat.card D - Nat.card B = n → D ⊓ transfiniteFiltration p δ ≤ B →
      (∀ (b : B) (β : Ordinal.{v}), β ≤ δ →
        ((f b:H) ∈ (transfiniteFiltration p β : AddSubgroup H) ↔
          (b:G) ∈ (transfiniteFiltration p β : AddSubgroup G))) → Result B C f hBD := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro B C f hBD hn hcut hpres
      let iBD : B → D := fun b => ⟨b,hBD b.property⟩
      have hiBD : Function.Injective iBD := by
        intro a b h
        exact Subtype.ext (congrArg (fun d : D => (d:G)) h)
      letI : Finite B := Finite.of_injective iBD hiBD
      dsimp only [Result]
      by_cases hDB : D ≤ B
      · let g : D →+ B :=
          { toFun := fun d => ⟨d,hDB d.property⟩
            map_zero' := rfl
            map_add' := fun _ _ => rfl }
        have hg : Function.Injective g := by
          intro a b h
          exact Subtype.ext (congrArg (fun z : B => (z:G)) h)
        let F : D →+ H := C.subtype.comp (f.toAddMonoidHom.comp g)
        refine ⟨F,Subtype.val_injective.comp (f.injective.comp hg),fun _ => rfl,?_⟩
        intro y β hβ
        exact hpres (g y) β hβ
      · obtain ⟨x,hxD,hxB,hpx,F,hF,hFa,hFp⟩ :=
          below_limit_extension G H p hG hH B D C f δ hδ hBD hDB hcut hpres hRank
        let S : AddSubgroup G := B ⊔ AddSubgroup.zmultiples x
        have hBS : B ≤ S := le_sup_left
        have hSD : S ≤ D := by
          intro y hy
          obtain ⟨b,hb,t,ht,hbt⟩ := AddSubgroup.mem_sup.mp hy
          obtain ⟨z,rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp ht
          rw [← hbt]
          exact D.add_mem (hBD hb) (D.zsmul_mem hxD z)
        let iSD : S → D := fun s => ⟨s,hSD s.property⟩
        have hiSD : Function.Injective iSD := by
          intro a b h
          exact Subtype.ext (congrArg (fun d : D => (d:G)) h)
        letI : Finite S := Finite.of_injective iSD hiSD
        let iBS : B → S := fun b => ⟨b,hBS b.property⟩
        have hiBS : Function.Injective iBS := by
          intro a b h
          exact Subtype.ext (congrArg (fun s : S => (s:G)) h)
        have hcardBS : Nat.card B < Nat.card S := by
          apply lt_of_le_of_ne (Nat.card_le_card_of_injective iBS hiBS)
          intro heq
          have hs := ((Nat.bijective_iff_injective_and_card iBS).mpr ⟨hiBS,heq⟩).2
          have hxS : x ∈ S := (le_sup_right : AddSubgroup.zmultiples x ≤ S) (AddSubgroup.mem_zmultiples x)
          obtain ⟨b,hb⟩ := hs ⟨x,hxS⟩
          have hbval := congrArg (fun s : S => (s:G)) hb
          change (b:G) = x at hbval
          exact hxB (hbval ▸ b.property)
        have hcardSD : Nat.card S ≤ Nat.card D := Nat.card_le_card_of_injective iSD hiSD
        have hsmall : Nat.card D - Nat.card S < n := by omega
        let e : S ≃+ F.range := AddEquiv.ofBijective F.rangeRestrict
          ⟨(fun a b h => hF (congrArg (fun z : F.range => (z:H)) h)), F.rangeRestrict_surjective⟩
        have hspres (s : S) (β : Ordinal.{v}) (hβ : β ≤ δ) :
            (e s:H) ∈ (transfiniteFiltration p β : AddSubgroup H) ↔
              (s:G) ∈ (transfiniteFiltration p β : AddSubgroup G) := hFp s β hβ
        obtain ⟨R,hR,hRa,hRp⟩ := ih (Nat.card D - Nat.card S) hsmall S F.range e hSD rfl
          (hcut.trans hBS) hspres
        refine ⟨R,hR,?_,hRp⟩
        intro b
        exact (hRa ⟨b,hBS b.property⟩).trans (hFa b)
  exact main (Nat.card D - Nat.card B) B C f hBD rfl hcut hpres

end LogicLineages.ModelsAlgebra.PGroups
