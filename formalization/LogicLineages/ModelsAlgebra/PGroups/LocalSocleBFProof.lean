module
public import LogicLineages.ModelsAlgebra.PGroups.LocalSocleBFTargets
public import LogicLineages.ModelsAlgebra.PGroups.BoundedSocleResponseProof
public import LogicLineages.ModelsAlgebra.PGroups.FiniteSocleReducedProof
public import LogicLineages.ModelsAlgebra.PGroups.PPrimaryFiniteGenerationProof
public import LogicLineages.ModelsAlgebra.PGroups.BackForthStructuralProof
public import LogicLineages.ModelsAlgebra.PGroups.BackForthCore
public import Mathlib.SetTheory.Ordinal.Principal
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth

private def OddStatement (γ : Ordinal) : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] [Countable G] [Countable H]
    (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → (∀ y : H, ∃ k : ℕ, p^k • y = 0) →
    ∀ (B : AddSubgroup G) (C : AddSubgroup H) [Finite B] (f : B ≃+ C),
    SoclesInfiniteBelow p G (Ordinal.omega0*γ) →
    SoclesInfiniteBelow p H (Ordinal.omega0*γ+Ordinal.omega0) →
    UlmRanksAgreeBelow p G H (Ordinal.omega0*γ) → MapCutsExact p f (Ordinal.omega0*γ) →
    MapCutsForward p f (Ordinal.omega0*γ+Ordinal.omega0) → SubgroupComparison f (2*γ+1)

private def EvenStatement (γ : Ordinal) : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] [Countable G] [Countable H]
    (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → (∀ y : H, ∃ k : ℕ, p^k • y = 0) →
    ∀ (B : AddSubgroup G) (C : AddSubgroup H) [Finite B] (f : B ≃+ C),
    SoclesInfiniteBelow p G (Ordinal.omega0*γ+Ordinal.omega0) →
    SoclesInfiniteBelow p H (Ordinal.omega0*γ+Ordinal.omega0) →
    UlmRanksAgreeBelow p G H (Ordinal.omega0*γ) →
    UlmRanksLeInterval p G H (Ordinal.omega0*γ) (Ordinal.omega0*γ+Ordinal.omega0) →
    MapCutsExact p f (Ordinal.omega0*γ+Ordinal.omega0) → SubgroupComparison f (2*γ+2)

private def LimitStatement (η : Ordinal) : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] [Countable G] [Countable H]
    (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → (∀ y : H, ∃ k : ℕ, p^k • y = 0) →
    ∀ (B : AddSubgroup G) (C : AddSubgroup H) [Finite B] (f : B ≃+ C),
    Order.IsSuccLimit η →
    SoclesInfiniteBelow p G (Ordinal.omega0*η) → SoclesInfiniteBelow p H (Ordinal.omega0*η) →
    UlmRanksAgreeBelow p G H (Ordinal.omega0*η) →
    MapCutsExact p f (Ordinal.omega0*η) → SubgroupComparison f η

private theorem subgroup_atomic {G H : Type} [AddCommGroup G] [AddCommGroup H]
    {B : AddSubgroup G} {C : AddSubgroup H} (f : B ≃+ C) : SubgroupComparison f 0 := by
  intro n b
  apply (zero_comparison H G n _ _).mpr
  have h₁ := embedding_atomic_agreement B H (C.subtype.comp f.toAddMonoidHom)
    (Subtype.val_injective.comp f.injective) n b
  have h₂ := embedding_atomic_agreement B G B.subtype Subtype.val_injective n b
  exact fun s t => (h₁ s t).symm.trans (h₂ s t)

private theorem inverse_exact {G H : Type} [AddCommGroup G] [AddCommGroup H]
    (p : ℕ) {D : AddSubgroup G} (F : D →+ H) (hF : Function.Injective F) (δ : Ordinal)
    (h : ∀ z : D, ∀ β ≤ δ, F z ∈ transfiniteFiltration p β ↔ (z:G) ∈ transfiniteFiltration p β) :
    MapCutsExact p (AddMonoidHom.ofInjective hF).symm δ := by
  intro c β hβ
  let e := AddMonoidHom.ofInjective hF
  have hv : F (e.symm c) = (c:H) := congrArg Subtype.val (e.apply_symm_apply c)
  have hh := h (e.symm c) β hβ
  rw [hv] at hh
  exact hh.symm

private theorem inverse_forward {G H : Type} [AddCommGroup G] [AddCommGroup H]
    (p : ℕ) {D : AddSubgroup G} (F : D →+ H) (hF : Function.Injective F) (δ : Ordinal)
    (h : ∀ z : D, ∀ β ≤ δ, F z ∈ transfiniteFiltration p β → (z:G) ∈ transfiniteFiltration p β) :
    MapCutsForward p (AddMonoidHom.ofInjective hF).symm δ := by
  intro c β hβ hc
  let e := AddMonoidHom.ofInjective hF
  have hv : F (e.symm c) = (c:H) := congrArg Subtype.val (e.apply_symm_apply c)
  exact h (e.symm c) β hβ (by rw [hv]; exact hc)

private theorem response_from_extension {G H : Type} [AddCommGroup G] [AddCommGroup H]
    {B D : AddSubgroup G} {C : AddSubgroup H} (f : B ≃+ C) (hBD : B ≤ D)
    (F : D →+ H) (hF : Function.Injective F)
    (hFa : ∀ b : B, F ⟨b,hBD b.property⟩ = (f b:H)) (α : Ordinal)
    (hr : SubgroupComparison (AddMonoidHom.ofInjective hF).symm α)
    (n : ℕ) (b : Fin n → B) (m : ℕ) (d : Fin m → G) (hd : ∀ i, d i ∈ D) :
    ∃ c : Fin m → H, BackAndForth α (append (fun i => (b i:G)) d)
      (append (fun i => (f (b i):H)) c) := by
  let e := AddMonoidHom.ofInjective hF
  let s : Fin (n+m) → D := append (fun i => ⟨b i,hBD (b i).property⟩) (fun i => ⟨d i,hd i⟩)
  let t : Fin (n+m) → F.range := fun i => e (s i)
  let c : Fin m → H := fun i => F ⟨d i,hd i⟩
  have hleft : (fun i => (e.symm (t i):G)) = append (fun i => (b i:G)) d := by
    funext i
    dsimp only [t]
    rw [AddEquiv.symm_apply_apply]
    induction i using Fin.addCases <;> simp [s,append]
  have hright : (fun i => (t i:H)) = append (fun i => (f (b i):H)) c := by
    funext i
    change F (s i) = _
    induction i using Fin.addCases <;> simp [s,c,append,hFa]
  have h := hr (n+m) t
  change BackAndForth α (fun i => (e.symm (t i):G)) (fun i => (t i:H)) at h
  rw [hleft,hright] at h
  exact ⟨c,h⟩

private theorem two_mul_limit {γ : Ordinal} (hγ : Order.IsSuccLimit γ) : 2*γ=γ := by
  obtain ⟨ζ,hζ⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hγ.isSuccPrelimit
  rw [hζ,← mul_assoc]
  have htwo : (2:Ordinal)*Ordinal.omega0 = Ordinal.omega0 := by
    exact_mod_cast (Ordinal.natCast_mul_omega0 (by decide : 0 < (2:ℕ)))
  rw [htwo]

theorem local_socle_back_forth : Targets.localSocleBackForth := by
  classical
  have main : ∀ γ : Ordinal, OddStatement γ ∧ EvenStatement γ ∧ LimitStatement γ := by
    intro γ
    induction γ using WellFoundedLT.induction with
    | ind γ ih =>
      have hlimit : LimitStatement γ := by
        intro G H _ _ _ _ p _ hG hH B C _ f hγ sG sH hRank hpres n b
        apply (positive_comparison γ hγ.ne_zero H G n _ _).mpr
        intro β hβ m d
        have hω : Ordinal.omega0*β ≤ Ordinal.omega0*γ :=
          (Ordinal.isNormal_mul_right Ordinal.omega0_pos).monotone hβ.le
        have hblock : Ordinal.omega0*β+Ordinal.omega0 ≤ Ordinal.omega0*γ := by
          simpa only [Order.succ_eq_add_one,mul_add_one] using
            (Ordinal.isNormal_mul_right Ordinal.omega0_pos).monotone (hγ.succ_lt hβ).le
        have ho := (ih β hβ).1 G H p hG hH B C f
          (fun ξ hξ => sG ξ (hξ.trans_le hω))
          (fun ξ hξ => sH ξ (hξ.trans_le hblock))
          (fun ξ hξ => hRank ξ (hξ.trans_le hω))
          (fun x ξ hξ => hpres x ξ (hξ.trans hω))
          (fun x ξ hξ => (hpres x ξ (hξ.trans hblock)).mpr) n b
        have hβodd : β < 2*β+1 := (Ordinal.le_mul_right β (by norm_num : (0:Ordinal)<2)).trans_lt
          (Order.lt_succ (2*β))
        have hoddpos : 2*β+1 ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le (Order.lt_succ (2*β)))
        exact (positive_comparison (2*β+1) hoddpos H G n _ _).mp ho β hβodd m d
      have hodd : OddStatement γ := by
        intro G H _ _ _ _ p _ hG hH B C _ f sG sH hRank hpres hforward n b
        apply (back_forth_successor (2*γ) H G n _ _).mpr
        intro m d
        let D : AddSubgroup G := B ⊔ AddSubgroup.closure (Set.range d)
        letI : Finite D := p_primary_finite_tuple_extension G p (Fact.out : p.Prime).ne_zero hG B m d
        have hBD : B ≤ D := le_sup_left
        have hd : ∀ i, d i ∈ D := fun i =>
          (le_sup_right : AddSubgroup.closure (Set.range d) ≤ D) (AddSubgroup.subset_closure ⟨i,rfl⟩)
        let δ : Ordinal := Ordinal.omega0*γ
        have hδ : δ=0 ∨ Order.IsSuccLimit δ := by
          by_cases hz : γ=0
          · left; simp [δ,hz]
          · right
            exact Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0
              (lt_of_le_of_ne zero_le (Ne.symm hz))
        obtain ⟨F,hF,hFa,hFp⟩ := bounded_socle_odd_response G H p hG hH (δ+Ordinal.omega0) sH D B C f δ hδ hBD
          ((add_lt_add_iff_left δ).mpr (Ordinal.natCast_lt_omega0 (Nat.card D)))
          hpres (fun x ξ hξ => hforward x ξ (hξ.trans
            (add_le_add (le_refl δ) (Ordinal.natCast_lt_omega0 (Nat.card D)).le)))
          (fun ξ hξ => (hRank ξ hξ).le)
        let e := AddMonoidHom.ofInjective hF
        letI : Finite F.range := Finite.of_surjective F.rangeRestrict F.rangeRestrict_surjective
        have hrev := inverse_exact p F hF δ hFp
        have sHlow : SoclesInfiniteBelow p H δ := fun ξ hξ =>
          sH ξ (hξ.trans_le (Ordinal.le_add_right δ Ordinal.omega0))
        have hr : SubgroupComparison e.symm (2*γ) := by
          rcases Ordinal.zero_or_succ_or_isSuccLimit γ with hz | ⟨β,hβ⟩ | hγ
          · subst γ
            simpa only [mul_zero] using subgroup_atomic e.symm
          · subst γ
            have hβlt : β < β+1 := Order.lt_succ β
            have hbound : Ordinal.omega0*β ≤ δ := by
              dsimp only [δ]
              exact (Ordinal.isNormal_mul_right Ordinal.omega0_pos).monotone hβlt.le
            have hblock : Ordinal.omega0*β+Ordinal.omega0 = δ := by simp only [δ,Order.succ_eq_add_one,mul_add_one]
            have hh := (ih β hβlt).2.1 H G p hH hG F.range D e.symm
              (by simpa only [hblock] using sHlow)
              (by simpa only [hblock] using sG)
              (fun ξ hξ => (hRank ξ (hξ.trans_le hbound)).symm)
              (fun ξ _ hξ => (hRank ξ (by simpa only [hblock] using hξ)).symm.le)
              (by simpa only [hblock] using hrev)
            simpa only [Order.succ_eq_add_one,mul_add_one] using hh
          · have hh := hlimit H G p hH hG F.range D e.symm hγ sHlow sG
              (fun ξ hξ => (hRank ξ hξ).symm) hrev
            rw [two_mul_limit hγ]
            exact hh
        exact response_from_extension f hBD F hF hFa (2*γ) hr n b m d hd
      have heven : EvenStatement γ := by
        intro G H _ _ _ _ p _ hG hH B C _ f sG sH hRank hLe hpres n b
        have heq : (2*γ+1)+1 = 2*γ+2 := by simp only [add_assoc,one_add_one_eq_two]
        rw [← heq]
        apply (back_forth_successor (2*γ+1) H G n _ _).mpr
        intro m d
        let D : AddSubgroup G := B ⊔ AddSubgroup.closure (Set.range d)
        letI : Finite D := p_primary_finite_tuple_extension G p (Fact.out : p.Prime).ne_zero hG B m d
        have hBD : B ≤ D := le_sup_left
        have hd : ∀ i, d i ∈ D := fun i =>
          (le_sup_right : AddSubgroup.closure (Set.range d) ≤ D) (AddSubgroup.subset_closure ⟨i,rfl⟩)
        let δ : Ordinal := Ordinal.omega0*γ
        have hRanks : ∀ ξ < δ+Ordinal.omega0,
            Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p ξ : AddSubgroup G)) ≤
            Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p ξ : AddSubgroup H)) := by
          intro ξ hξ
          by_cases hlo : ξ < δ
          · exact (hRank ξ hlo).le
          · exact hLe ξ (le_of_not_gt hlo) hξ
        obtain ⟨F,hF,hFa,hFp,hFback⟩ := bounded_socle_even_response G H p hG hH (δ+Ordinal.omega0) sH D B C f δ hBD le_rfl hpres hRanks
        let e := AddMonoidHom.ofInjective hF
        letI : Finite F.range := Finite.of_surjective F.rangeRestrict F.rangeRestrict_surjective
        have hr := hodd H G p hH hG F.range D e.symm
          (fun ξ hξ => sH ξ (hξ.trans_le (Ordinal.le_add_right δ Ordinal.omega0))) sG
          (fun ξ hξ => (hRank ξ hξ).symm)
          (inverse_exact p F hF δ hFp)
          (inverse_forward p F hF (δ+Ordinal.omega0) hFback)
        exact response_from_extension f hBD F hF hFa (2*γ+1) hr n b m d hd
      exact ⟨hodd,heven,hlimit⟩
  intro G H _ _ _ _ p _ hG hH B C _ f
  exact ⟨fun γ => (main γ).1 G H p hG hH B C f,
    fun γ => (main γ).2.1 G H p hG hH B C f,
    fun η => (main η).2.2 G H p hG hH B C f⟩

private theorem omega_mul_zero_or_limit (γ : Ordinal) :
    Ordinal.omega0*γ=0 ∨ Order.IsSuccLimit (Ordinal.omega0*γ) := by
  by_cases hγ : γ=0
  · left; simp [hγ]
  · right
    exact Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0
      (lt_of_le_of_ne zero_le (Ne.symm hγ))

private theorem socles_of_long (G : Type) [AddCommGroup G] (p : ℕ) [Fact p.Prime]
    (hG : ∀ x : G, ∃ k : ℕ, p^k • x = 0) (hr : IsReducedAddGroup G)
    (δ : Ordinal) (hδ : δ=0 ∨ Order.IsSuccLimit δ) (hl : StagesNonzeroBelow p G δ) :
    SoclesInfiniteBelow p G δ := by
  rcases hδ with rfl | hδ
  · intro α hα
    exact False.elim (not_lt_of_ge zero_le hα)
  · exact reduced_long_limit_infinite_socles G p hG hr δ hδ hl

theorem reduced_long_back_forth : Targets.reducedLongBackForth := by
  intro G H _ _ _ _ p _ hG hH rG rH B C _ f
  have h := local_socle_back_forth G H p hG hH B C f
  refine ⟨?_,?_,?_⟩
  · intro γ lG lH hR hE hF
    exact h.1 γ
      (socles_of_long G p hG rG _ (omega_mul_zero_or_limit γ) lG)
      (socles_of_long H p hH rH _ (Or.inr (Ordinal.isSuccLimit_add _ Ordinal.isSuccLimit_omega0)) lH)
      hR hE hF
  · intro γ lG lH hR hL hE
    exact h.2.1 γ
      (socles_of_long G p hG rG _ (Or.inr (Ordinal.isSuccLimit_add _ Ordinal.isSuccLimit_omega0)) lG)
      (socles_of_long H p hH rH _ (Or.inr (Ordinal.isSuccLimit_add _ Ordinal.isSuccLimit_omega0)) lH)
      hR hL hE
  · intro η hη lG lH hR hE
    exact h.2.2 η hη
      (socles_of_long G p hG rG _ (omega_mul_zero_or_limit η) lG)
      (socles_of_long H p hH rH _ (omega_mul_zero_or_limit η) lH)
      hR hE

theorem reduced_limit_cut_comparison : Targets.reducedLimitCutComparison := by
  intro G H _ _ _ _ p _ hG hH rG rH B C _ f γ lG lH hRank hpres
  have h := reduced_long_back_forth G H p hG hH rG rH B C f
  rcases Ordinal.zero_or_succ_or_isSuccLimit γ with hz | ⟨β,hβ⟩ | hγ
  · subst γ
    simpa only [mul_zero] using subgroup_atomic f
  · subst γ
    have hblock : Ordinal.omega0*β+Ordinal.omega0 = Ordinal.omega0*Order.succ β := by
      simp only [Order.succ_eq_add_one,mul_add_one]
    have hbound : Ordinal.omega0*β ≤ Ordinal.omega0*Order.succ β :=
      (Ordinal.isNormal_mul_right Ordinal.omega0_pos).monotone (Order.le_succ β)
    have hh := h.2.1 β
      (by simpa only [hblock] using lG) (by simpa only [hblock] using lH)
      (fun ξ hξ => hRank ξ (hξ.trans_le hbound))
      (fun ξ _ hξ => (hRank ξ (by simpa only [hblock] using hξ)).le)
      (by simpa only [hblock] using hpres)
    simpa only [Order.succ_eq_add_one,mul_add_one] using hh
  · rw [two_mul_limit hγ]
    exact h.2.2 γ hγ lG lH hRank hpres

end LogicLineages.ModelsAlgebra.PGroups
