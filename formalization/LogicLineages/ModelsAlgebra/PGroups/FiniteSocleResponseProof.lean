module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteSocleResponseTargets
public import LogicLineages.ModelsAlgebra.PGroups.HeadroomExtensionProof
public import LogicLineages.ModelsAlgebra.PGroups.FiniteOmegaBoundProof
public import LogicLineages.ModelsAlgebra.PGroups.BelowLimitExtension
public meta import Lean.Elab.Tactic.Omega
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

private theorem select_proper (G : Type) [AddCommGroup G] (p : ℕ)
    (hG : ∀ y : G, ∃ n : ℕ, p^n • y = 0)
    (B D : AddSubgroup G) [Finite B] (hBD : B ≤ D) (hnot : ¬D ≤ B) :
    ∃ x : G, x ∈ D ∧ x ∉ B ∧ p • x ∈ B ∧
      (∀ (b : B) (β : Ordinal.{0}), x+b ∈ transfiniteFiltration p β →
        x ∈ transfiniteFiltration p β) ∧
      (∀ b : B,
        (∀ (c : B) (β : Ordinal.{0}), x+c ∈ transfiniteFiltration p β →
          x+b ∈ transfiniteFiltration p β) →
        ∀ β : Ordinal.{0}, p • (x+b) ∈ transfiniteFiltration p β →
          p • x ∈ transfiniteFiltration p β) := by
  obtain ⟨y,hyD,hyB,hpy⟩ := power_step_selection G p hG B D hBD hnot
  obtain ⟨b,hb,hpb⟩ := coset_double_maximum G p B y
  let x : G := y+b
  have hxD : x ∈ D := D.add_mem hyD (hBD b.property)
  have hxB : x ∉ B := by
    intro hx
    exact hyB (by simpa only [x,add_sub_cancel_right] using B.sub_mem hx b.property)
  have hpx : p • x ∈ B := by
    change p • (y+(b:G)) ∈ B
    rw [smul_add]
    exact B.add_mem hpy (B.nsmul_mem b.property p)
  refine ⟨x,hxD,hxB,hpx,?_,?_⟩
  · intro c β hc
    apply hb (b+c) β
    simpa only [x,AddSubgroup.coe_add,add_assoc] using hc
  · intro c hc β hpc
    have hcmax : ∀ (d : B) (γ : Ordinal.{0}),
        y+d ∈ transfiniteFiltration p γ → y+(b+c:B) ∈ transfiniteFiltration p γ := by
      intro d γ hd
      have he : x + ((d-b:B):G) = y+(d:G) := by
        change (y+(b:G))+((d:G)-(b:G)) = y+(d:G)
        abel
      have hm : x + ((d-b:B):G) ∈ transfiniteFiltration p γ := by rw [he]; exact hd
      have hr := hc (d-b) γ hm
      simpa only [x,AddSubgroup.coe_add,add_assoc] using hr
    exact hpb (b+c) hcmax β (by simpa only [x,AddSubgroup.coe_add,add_assoc] using hpc)

private theorem proper_high_mem_old (G : Type) [AddCommGroup G] (p : ℕ) [Fact p.Prime]
    (hG : ∀ y : G, ∃ n : ℕ, p^n • y = 0) (B : AddSubgroup G) (x : G)
    (hpx : p • x ∈ B) (δ : Ordinal.{0}) (hx : x ∉ transfiniteFiltration p δ)
    (hproper : ∀ (b : B) (β : Ordinal.{0}), x+b ∈ transfiniteFiltration p β →
      x ∈ transfiniteFiltration p β)
    (z : ↥(B ⊔ AddSubgroup.zmultiples x)) (hz : (z:G) ∈ transfiniteFiltration p δ) :
    (z:G) ∈ B := by
  obtain ⟨b,hb,t,ht,hbt⟩ := AddSubgroup.mem_sup.mp z.property
  obtain ⟨k,rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp ht
  by_cases hk : (p:ℤ) ∣ k
  · obtain ⟨j,hj⟩ := hk
    rw [← hbt]
    apply B.add_mem hb
    rw [hj,Int.mul_comm,mul_smul,natCast_zsmul]
    exact B.zsmul_mem hpx j
  · have hcop : Nat.Coprime k.natAbs p := by
      apply Nat.Coprime.symm
      apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      intro h
      exact hk (Int.natCast_dvd.mpr h)
    have hm : k • x + b ∈ transfiniteFiltration p δ := by
      rw [← hbt] at hz
      simpa only [add_comm] using hz
    exact False.elim (hx ((proper_coset_sum_membership G p hG B x hproper k hcop ⟨b,hb⟩ δ).mp hm).1)

theorem finite_socle_odd_response : Targets.finiteSocleOddResponse := by
  classical
  intro G H _ _ p _ hG hH hsoc D _ B C f δ hδ hBD hpres hforward hRank
  let Result (B : AddSubgroup G) (C : AddSubgroup H) (f : B ≃+ C) (hBD : B ≤ D) : Prop :=
    ∃ F : D →+ H, Function.Injective F ∧
      (∀ b : B, F ⟨b,hBD b.property⟩ = (f b:H)) ∧
      ∀ (y : D) (β : Ordinal.{0}), β ≤ δ →
        (F y ∈ transfiniteFiltration p β ↔ (y:G) ∈ transfiniteFiltration p β)
  have main : ∀ n : ℕ, ∀ (B : AddSubgroup G) (C : AddSubgroup H) (f : B ≃+ C) (hBD : B ≤ D),
      Nat.card D - Nat.card B = n →
      (∀ (b : B) (β : Ordinal.{0}), β ≤ δ →
        ((f b:H) ∈ transfiniteFiltration p β ↔ (b:G) ∈ transfiniteFiltration p β)) →
      (∀ (b : B) (β : Ordinal.{0}), β ≤ δ+(n:Ordinal) →
        (b:G) ∈ transfiniteFiltration p β → (f b:H) ∈ transfiniteFiltration p β) →
      Result B C f hBD := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro B C f hBD hn hpres hforward
      let iBD : B → D := fun b => ⟨b,hBD b.property⟩
      have hiBD : Function.Injective iBD := fun a b h =>
        Subtype.ext (congrArg (fun d : D => (d:G)) h)
      letI : Finite B := Finite.of_injective iBD hiBD
      dsimp only [Result]
      by_cases hDB : D ≤ B
      · let g : D →+ B :=
          { toFun := fun d => ⟨d,hDB d.property⟩
            map_zero' := rfl
            map_add' := fun _ _ => rfl }
        have hg : Function.Injective g := fun a b h =>
          Subtype.ext (congrArg (fun z : B => (z:G)) h)
        let F : D →+ H := C.subtype.comp (f.toAddMonoidHom.comp g)
        exact ⟨F,Subtype.val_injective.comp (f.injective.comp hg),fun _ => rfl,
          fun y β hβ => hpres (g y) β hβ⟩
      · obtain ⟨x,hxD,hxB,hpx,hproper,hmax⟩ := select_proper G p hG B D hBD hDB
        let S : AddSubgroup G := B ⊔ AddSubgroup.zmultiples x
        have hBS : B ≤ S := le_sup_left
        have hSD : S ≤ D := by
          intro y hy
          obtain ⟨b,hb,t,ht,hbt⟩ := AddSubgroup.mem_sup.mp hy
          obtain ⟨z,rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp ht
          rw [← hbt]
          exact D.add_mem (hBD hb) (D.zsmul_mem hxD z)
        let iSD : S → D := fun s => ⟨s,hSD s.property⟩
        have hiSD : Function.Injective iSD := fun a b h =>
          Subtype.ext (congrArg (fun d : D => (d:G)) h)
        letI : Finite S := Finite.of_injective iSD hiSD
        let iBS : B → S := fun b => ⟨b,hBS b.property⟩
        have hiBS : Function.Injective iBS := fun a b h =>
          Subtype.ext (congrArg (fun s : S => (s:G)) h)
        have hcardBS : Nat.card B < Nat.card S := by
          apply lt_of_le_of_ne (Nat.card_le_card_of_injective iBS hiBS)
          intro heq
          have hsur := ((Nat.bijective_iff_injective_and_card iBS).mpr ⟨hiBS,heq⟩).2
          have hxS : x ∈ S := (le_sup_right : AddSubgroup.zmultiples x ≤ S) (AddSubgroup.mem_zmultiples x)
          obtain ⟨b,hb⟩ := hsur ⟨x,hxS⟩
          have hbval := congrArg (fun s : S => (s:G)) hb
          change (b:G) = x at hbval
          exact hxB (hbval ▸ b.property)
        have hcardSD : Nat.card S ≤ Nat.card D := Nat.card_le_card_of_injective iSD hiSD
        let m := Nat.card D - Nat.card S
        have hsmall : m < n := by dsimp only [m]; omega
        let ρ : Ordinal := δ+(m:Ordinal)
        have hδρ : δ ≤ ρ := Ordinal.le_add_right δ _
        have hbudget : ρ+1 ≤ δ+(n:Ordinal) := by
          have hmn : ((m+1:ℕ):Ordinal) ≤ (n:Ordinal) := by exact_mod_cast Nat.succ_le_of_lt hsmall
          simpa only [ρ,Nat.cast_add,Nat.cast_one,add_assoc] using add_le_add (le_refl δ) hmn
        have hfw (b : B) (β : Ordinal) (hβ : β ≤ ρ+1) :
            (b:G) ∈ transfiniteFiltration p β → (f b:H) ∈ transfiniteFiltration p β :=
          hforward b β (hβ.trans hbudget)
        have hext : ∃ F : S →+ H, Function.Injective F ∧
            (∀ b : B, F ⟨b,hBS b.property⟩ = (f b:H)) ∧
            (∀ z : S, ∀ β ≤ δ, F z ∈ transfiniteFiltration p β ↔ (z:G) ∈ transfiniteFiltration p β) ∧
            (∀ z : S, ∀ β ≤ ρ, (z:G) ∈ transfiniteFiltration p β → F z ∈ transfiniteFiltration p β) := by
          by_cases hxcut : x ∈ transfiniteFiltration p δ
          · have hex : ∃ α : Ordinal, δ ≤ α ∧ α ≤ ρ ∧ x ∈ transfiniteFiltration p α ∧
                (x ∉ transfiniteFiltration p (α+1) ∨ α=ρ) := by
              by_cases hxρ : x ∈ transfiniteFiltration p ρ
              · exact ⟨ρ,hδρ,le_rfl,hxρ,Or.inr rfl⟩
              · obtain ⟨α,hαρ,hxa,hxan⟩ := exact_height_below_cut G p ρ x hxρ
                have hδα : δ ≤ α := by
                  by_contra hn
                  exact hxan (transfiniteFiltration_antitone p
                    (Order.add_one_le_iff.mpr (lt_of_not_ge hn)) hxcut)
                exact ⟨α,hδα,hαρ.le,hxa,Or.inl hxan⟩
            obtain ⟨α,hδα,hαρ,hxa,hcap⟩ := hex
            exact one_unit_headroom_extension G H p hG B C f δ α ρ hδα hαρ hpres hfw
              x hxB hxa hcap hproper hpx (hsoc α)
          · obtain ⟨α,hαδ,hxa,hxan⟩ := exact_height_below_cut G p δ x hxcut
            have hlim : Order.IsSuccLimit δ := hδ.resolve_left (fun he => by simpa [he] using hαδ)
            have hα2 : α+1+1 ≤ δ := (hlim.succ_lt (hlim.succ_lt hαδ)).le
            have hlow : ∃ F : S →+ H, Function.Injective F ∧
                (∀ b : B, F ⟨b,hBS b.property⟩ = (f b:H)) ∧
                ∀ z : S, ∀ β ≤ δ, F z ∈ transfiniteFiltration p β ↔ (z:G) ∈ transfiniteFiltration p β := by
              by_cases hgap : p • x ∈ transfiniteFiltration p (α+1+1)
              · exact socle_gap_preserving_extension G H p B C x α δ hG hH hα2 hxB hpx f hpres
                  (hRank α hαδ) hxa hxan hgap hproper
              · have hpx1 : p • x ∈ transfiniteFiltration p (α+1) := by
                  rw [transfiniteFiltration_add_one]
                  exact ⟨x,hxa,rfl⟩
                let g : B →+ H := C.subtype.comp f.toAddMonoidHom
                exact successor_preserving_extension G H p B x α δ hG hH hα2 hxB hpx g
                  (Subtype.val_injective.comp f.injective) hpres hxa hxan hpx1 hgap hproper hmax
            obtain ⟨F,hF,hFa,hFp⟩ := hlow
            refine ⟨F,hF,hFa,hFp,?_⟩
            intro z β hβ hz
            by_cases hβδ : β ≤ δ
            · exact (hFp z β hβδ).mpr hz
            · have hzδ := transfiniteFiltration_antitone p (le_of_not_ge hβδ) hz
              have hzB := proper_high_mem_old G p hG B x hpx δ hxcut hproper z hzδ
              have he : F z = (f ⟨z,hzB⟩:H) := hFa ⟨z,hzB⟩
              rw [he]
              exact hfw ⟨z,hzB⟩ β (hβ.trans (Order.le_succ ρ)) hz
        obtain ⟨F,hF,hFa,hFp,hFfw⟩ := hext
        let e : S ≃+ F.range := AddEquiv.ofBijective F.rangeRestrict
          ⟨(fun a b h => hF (congrArg (fun z : F.range => (z:H)) h)),F.rangeRestrict_surjective⟩
        obtain ⟨R,hR,hRa,hRp⟩ := ih m hsmall S F.range e hSD rfl hFp hFfw
        refine ⟨R,hR,?_,hRp⟩
        intro b
        exact (hRa ⟨b,hBS b.property⟩).trans (hFa b)
  apply main (Nat.card D-Nat.card B) B C f hBD rfl hpres
  intro b β hβ
  apply hforward b β (hβ.trans (add_le_add (le_refl δ) ?_))
  exact_mod_cast Nat.sub_le (Nat.card D) (Nat.card B)


theorem finite_socle_gap_response : Targets.finiteSocleGapResponse := by
  classical
  intro G H _ _ p _ hG hH hsoc D _ B C f lam hgapD hBD hpres hforward hRank
  let δ : Ordinal := lam+1
  let Result (B : AddSubgroup G) (C : AddSubgroup H) (f : B ≃+ C) (hBD : B ≤ D) : Prop :=
    ∃ F : D →+ H, Function.Injective F ∧
      (∀ b : B, F ⟨b,hBD b.property⟩ = (f b:H)) ∧
      ∀ (y : D) (β : Ordinal.{0}), β ≤ δ →
        (F y ∈ transfiniteFiltration p β ↔ (y:G) ∈ transfiniteFiltration p β)
  have main : ∀ n : ℕ, ∀ (B : AddSubgroup G) (C : AddSubgroup H) (f : B ≃+ C) (hBD : B ≤ D),
      Nat.card D - Nat.card B = n →
      (∀ (b : B) (β : Ordinal.{0}), β ≤ δ →
        ((f b:H) ∈ transfiniteFiltration p β ↔ (b:G) ∈ transfiniteFiltration p β)) →
      (∀ (b : B) (β : Ordinal.{0}), β ≤ δ+(n:Ordinal) →
        (b:G) ∈ transfiniteFiltration p β → (f b:H) ∈ transfiniteFiltration p β) →
      Result B C f hBD := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro B C f hBD hn hpres hforward
      let iBD : B → D := fun b => ⟨b,hBD b.property⟩
      have hiBD : Function.Injective iBD := fun a b h =>
        Subtype.ext (congrArg (fun d : D => (d:G)) h)
      letI : Finite B := Finite.of_injective iBD hiBD
      dsimp only [Result]
      by_cases hDB : D ≤ B
      · let g : D →+ B :=
          { toFun := fun d => ⟨d,hDB d.property⟩
            map_zero' := rfl
            map_add' := fun _ _ => rfl }
        have hg : Function.Injective g := fun a b h =>
          Subtype.ext (congrArg (fun z : B => (z:G)) h)
        let F : D →+ H := C.subtype.comp (f.toAddMonoidHom.comp g)
        exact ⟨F,Subtype.val_injective.comp (f.injective.comp hg),fun _ => rfl,
          fun y β hβ => hpres (g y) β hβ⟩
      · obtain ⟨x,hxD,hxB,hpx,hproper,hmax⟩ := select_proper G p hG B D hBD hDB
        let S : AddSubgroup G := B ⊔ AddSubgroup.zmultiples x
        have hBS : B ≤ S := le_sup_left
        have hSD : S ≤ D := by
          intro y hy
          obtain ⟨b,hb,t,ht,hbt⟩ := AddSubgroup.mem_sup.mp hy
          obtain ⟨z,rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp ht
          rw [← hbt]
          exact D.add_mem (hBD hb) (D.zsmul_mem hxD z)
        let iSD : S → D := fun s => ⟨s,hSD s.property⟩
        have hiSD : Function.Injective iSD := fun a b h =>
          Subtype.ext (congrArg (fun d : D => (d:G)) h)
        letI : Finite S := Finite.of_injective iSD hiSD
        let iBS : B → S := fun b => ⟨b,hBS b.property⟩
        have hiBS : Function.Injective iBS := fun a b h =>
          Subtype.ext (congrArg (fun s : S => (s:G)) h)
        have hcardBS : Nat.card B < Nat.card S := by
          apply lt_of_le_of_ne (Nat.card_le_card_of_injective iBS hiBS)
          intro heq
          have hsur := ((Nat.bijective_iff_injective_and_card iBS).mpr ⟨hiBS,heq⟩).2
          have hxS : x ∈ S := (le_sup_right : AddSubgroup.zmultiples x ≤ S) (AddSubgroup.mem_zmultiples x)
          obtain ⟨b,hb⟩ := hsur ⟨x,hxS⟩
          have hbval := congrArg (fun s : S => (s:G)) hb
          change (b:G) = x at hbval
          exact hxB (hbval ▸ b.property)
        have hcardSD : Nat.card S ≤ Nat.card D := Nat.card_le_card_of_injective iSD hiSD
        let m := Nat.card D - Nat.card S
        have hsmall : m < n := by dsimp only [m]; omega
        let ρ : Ordinal := δ+(m:Ordinal)
        have hδρ : δ ≤ ρ := Ordinal.le_add_right δ _
        have hbudget : ρ+1 ≤ δ+(n:Ordinal) := by
          have hmn : ((m+1:ℕ):Ordinal) ≤ (n:Ordinal) := by exact_mod_cast Nat.succ_le_of_lt hsmall
          simpa only [ρ,Nat.cast_add,Nat.cast_one,add_assoc] using add_le_add (le_refl δ) hmn
        have hfw (b : B) (β : Ordinal) (hβ : β ≤ ρ+1) :
            (b:G) ∈ transfiniteFiltration p β → (f b:H) ∈ transfiniteFiltration p β :=
          hforward b β (hβ.trans hbudget)
        have hext : ∃ F : S →+ H, Function.Injective F ∧
            (∀ b : B, F ⟨b,hBS b.property⟩ = (f b:H)) ∧
            (∀ z : S, ∀ β ≤ δ, F z ∈ transfiniteFiltration p β ↔ (z:G) ∈ transfiniteFiltration p β) ∧
            (∀ z : S, ∀ β ≤ ρ, (z:G) ∈ transfiniteFiltration p β → F z ∈ transfiniteFiltration p β) := by
          by_cases hxcut : x ∈ transfiniteFiltration p δ
          · have hex : ∃ α : Ordinal, δ ≤ α ∧ α ≤ ρ ∧ x ∈ transfiniteFiltration p α ∧
                (x ∉ transfiniteFiltration p (α+1) ∨ α=ρ) := by
              by_cases hxρ : x ∈ transfiniteFiltration p ρ
              · exact ⟨ρ,hδρ,le_rfl,hxρ,Or.inr rfl⟩
              · obtain ⟨α,hαρ,hxa,hxan⟩ := exact_height_below_cut G p ρ x hxρ
                have hδα : δ ≤ α := by
                  by_contra hn
                  exact hxan (transfiniteFiltration_antitone p
                    (Order.add_one_le_iff.mpr (lt_of_not_ge hn)) hxcut)
                exact ⟨α,hδα,hαρ.le,hxa,Or.inl hxan⟩
            obtain ⟨α,hδα,hαρ,hxa,hcap⟩ := hex
            exact one_unit_headroom_extension G H p hG B C f δ α ρ hδα hαρ hpres hfw
              x hxB hxa hcap hproper hpx (hsoc α)
          · have hxlam : x ∉ transfiniteFiltration p lam := by
              intro hxl
              have hm : x ∈ D ⊓ transfiniteFiltration p lam := ⟨hxD,hxl⟩
              rw [hgapD] at hm
              exact hxcut hm.2
            obtain ⟨α,hαδ,hxa,hxan⟩ := exact_height_below_cut G p lam x hxlam
            have hα2 : α+1+1 ≤ δ := add_le_add (Order.add_one_le_iff.mpr hαδ) le_rfl
            have hlow : ∃ F : S →+ H, Function.Injective F ∧
                (∀ b : B, F ⟨b,hBS b.property⟩ = (f b:H)) ∧
                ∀ z : S, ∀ β ≤ δ, F z ∈ transfiniteFiltration p β ↔ (z:G) ∈ transfiniteFiltration p β := by
              by_cases hgap : p • x ∈ transfiniteFiltration p (α+1+1)
              · exact socle_gap_preserving_extension G H p B C x α δ hG hH hα2 hxB hpx f hpres
                  (hRank α hαδ) hxa hxan hgap hproper
              · have hpx1 : p • x ∈ transfiniteFiltration p (α+1) := by
                  rw [transfiniteFiltration_add_one]
                  exact ⟨x,hxa,rfl⟩
                let g : B →+ H := C.subtype.comp f.toAddMonoidHom
                exact successor_preserving_extension G H p B x α δ hG hH hα2 hxB hpx g
                  (Subtype.val_injective.comp f.injective) hpres hxa hxan hpx1 hgap hproper hmax
            obtain ⟨F,hF,hFa,hFp⟩ := hlow
            refine ⟨F,hF,hFa,hFp,?_⟩
            intro z β hβ hz
            by_cases hβδ : β ≤ δ
            · exact (hFp z β hβδ).mpr hz
            · have hzδ := transfiniteFiltration_antitone p (le_of_not_ge hβδ) hz
              have hzB := proper_high_mem_old G p hG B x hpx δ hxcut hproper z hzδ
              have he : F z = (f ⟨z,hzB⟩:H) := hFa ⟨z,hzB⟩
              rw [he]
              exact hfw ⟨z,hzB⟩ β (hβ.trans (Order.le_succ ρ)) hz
        obtain ⟨F,hF,hFa,hFp,hFfw⟩ := hext
        let e : S ≃+ F.range := AddEquiv.ofBijective F.rangeRestrict
          ⟨(fun a b h => hF (congrArg (fun z : F.range => (z:H)) h)),F.rangeRestrict_surjective⟩
        obtain ⟨R,hR,hRa,hRp⟩ := ih m hsmall S F.range e hSD rfl hFp hFfw
        refine ⟨R,hR,?_,hRp⟩
        intro b
        exact (hRa ⟨b,hBS b.property⟩).trans (hFa b)
  apply main (Nat.card D-Nat.card B) B C f hBD rfl hpres
  intro b β hβ
  apply hforward b β (hβ.trans (add_le_add (le_refl δ) ?_))
  exact_mod_cast Nat.sub_le (Nat.card D) (Nat.card B)


theorem finite_socle_even_response : Targets.finiteSocleEvenResponse := by
  intro G H _ _ p _ hG hH hsoc D _ B C f δ hBD hpres hRank
  obtain ⟨N,hN⟩ := finite_omega_block_bound G p D δ
  let lam : Ordinal := δ+(N:Ordinal)
  have hgap : D ⊓ transfiniteFiltration p lam = D ⊓ transfiniteFiltration p (lam+1) := by
    apply (hN N le_rfl).trans
    simpa only [lam,Nat.cast_add,Nat.cast_one,add_assoc] using (hN (N+1) (Nat.le_succ N)).symm
  have hlam : lam < δ+Ordinal.omega0 :=
    (add_lt_add_iff_left δ).mpr (Ordinal.natCast_lt_omega0 N)
  have hbudget : lam+1+(Nat.card D:Ordinal) < δ+Ordinal.omega0 := by
    have h := (add_lt_add_iff_left δ).mpr (Ordinal.natCast_lt_omega0 (N+1+Nat.card D))
    simpa only [lam,Nat.cast_add,Nat.cast_one,add_assoc] using h
  have hcut : lam+1 ≤ δ+Ordinal.omega0 :=
    (Ordinal.le_add_right (lam+1) (Nat.card D:Ordinal)).trans hbudget.le
  obtain ⟨F,hF,hFa,hFp⟩ := finite_socle_gap_response G H p hG hH hsoc D B C f lam hgap hBD
    (fun b β hβ => hpres b β (hβ.trans hcut))
    (fun b β hβ => (hpres b β (hβ.trans hbudget.le)).mpr)
    (fun α hα => hRank α (hα.trans hlam))
  have hδcut : δ ≤ lam+1 := (Ordinal.le_add_right δ (N:Ordinal)).trans (Order.le_succ lam)
  refine ⟨F,hF,hFa,?_,?_⟩
  · intro z β hβ
    exact hFp z β (hβ.trans hδcut)
  · intro z β hβ hz
    by_cases hβcut : β ≤ lam+1
    · exact (hFp z β hβcut).mp hz
    · have htarget := transfiniteFiltration_antitone p (le_of_not_ge hβcut) hz
      have hsource := (hFp z (lam+1) le_rfl).mp htarget
      have hm : (z:G) ∈ D ⊓ transfiniteFiltration p (δ+((N+1:ℕ):Ordinal)) := by
        refine ⟨z.property,?_⟩
        change (z:G) ∈ transfiniteFiltration p (lam+1) at hsource
        simp only [lam,Nat.cast_add,Nat.cast_one,add_assoc] at hsource ⊢
        exact hsource
      rw [hN (N+1) (Nat.le_succ N)] at hm
      exact transfiniteFiltration_antitone p hβ hm.2


end LogicLineages.ModelsAlgebra.PGroups
