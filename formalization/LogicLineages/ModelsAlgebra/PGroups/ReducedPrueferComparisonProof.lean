module
public import LogicLineages.ModelsAlgebra.PGroups.ReducedPrueferComparisonTargets
public import LogicLineages.ModelsAlgebra.PGroups.PrueferEnlargementProof
public import LogicLineages.ModelsAlgebra.PGroups.LocalSocleBFProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth
private theorem subgroup_atomic {G H : Type} [AddCommGroup G] [AddCommGroup H]
    {B : AddSubgroup G} {C : AddSubgroup H} (f : B ≃+ C) : SubgroupComparison f 0 := by
  intro n b
  apply (zero_comparison H G n _ _).mpr
  have h₁ := embedding_atomic_agreement B H (C.subtype.comp f.toAddMonoidHom)
    (Subtype.val_injective.comp f.injective) n b
  have h₂ := embedding_atomic_agreement B G B.subtype Subtype.val_injective n b
  exact fun s t => (h₁ s t).symm.trans (h₂ s t)

private theorem two_mul_limit {γ : Ordinal} (hγ : Order.IsSuccLimit γ) : 2*γ=γ := by
  obtain ⟨ζ,hζ⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hγ.isSuccPrelimit
  rw [hζ,← mul_assoc]
  have htwo : (2:Ordinal)*Ordinal.omega0 = Ordinal.omega0 := by
    exact_mod_cast (Ordinal.natCast_mul_omega0 (by decide : 0 < (2:ℕ)))
  rw [htwo]

private theorem local_cut (G H : Type) [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H] (p:ℕ) [Fact p.Prime]
    (hG:∀x:G,∃k:ℕ,p^k • x=0) (hH:∀x:H,∃k:ℕ,p^k • x=0)
    (B:AddSubgroup G) (C:AddSubgroup H) [Finite B] (f:B≃+C) (γ:Ordinal.{0})
    (sG:SoclesInfiniteBelow p G (Ordinal.omega0*γ))
    (sH:SoclesInfiniteBelow p H (Ordinal.omega0*γ))
    (hRank:UlmRanksAgreeBelow p G H (Ordinal.omega0*γ))
    (hpres:MapCutsExact p f (Ordinal.omega0*γ)) : SubgroupComparison f (2*γ) := by
  have h := local_socle_back_forth G H p hG hH B C f
  rcases Ordinal.zero_or_succ_or_isSuccLimit γ with hz | ⟨β,hβ⟩ | hγ
  · subst γ
    simpa only [mul_zero] using subgroup_atomic f
  · subst γ
    have hblock : Ordinal.omega0*β+Ordinal.omega0 = Ordinal.omega0*Order.succ β := by
      simp only [Order.succ_eq_add_one,mul_add_one]
    have hbound : Ordinal.omega0*β ≤ Ordinal.omega0*Order.succ β :=
      (Ordinal.isNormal_mul_right Ordinal.omega0_pos).monotone (Order.le_succ β)
    have hh := h.2.1 β
      (by simpa only [hblock] using sG) (by simpa only [hblock] using sH)
      (fun ξ hξ => hRank ξ (hξ.trans_le hbound))
      (fun ξ _ hξ => (hRank ξ (by simpa only [hblock] using hξ)).le)
      (by simpa only [hblock] using hpres)
    simpa only [Order.succ_eq_add_one,mul_add_one] using hh
  · rw [two_mul_limit hγ]
    exact h.2.2 γ hγ sG sH hRank hpres

theorem reduced_pruefer_comparison : Targets.reducedPrueferComparison := by
  classical
  intro G _ _ p _ hG hr γ hl n a
  let Q := G×PrueferModel p
  have hd := pruefer_enlargement_data G p hG
  letI : Countable Q := hd.1
  have sG : SoclesInfiniteBelow p G (Ordinal.omega0*γ) := by
    by_cases hz:γ=0
    · intro α hα
      simp only [hz,mul_zero,not_lt_zero] at hα
    · exact reduced_long_limit_infinite_socles G p hG hr _
        (Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 (lt_of_le_of_ne zero_le (Ne.symm hz))) hl
  have sQ : SoclesInfiniteBelow p Q (Ordinal.omega0*γ) := by
    intro α hα
    letI := sG α hα
    let j : pSocle p (transfiniteFiltration p α : AddSubgroup G) →
        pSocle p (transfiniteFiltration p α : AddSubgroup Q) := fun x =>
      ⟨((x:G),0),(hd.2.2.1 α _).mpr x.property.1,by
        change p • ((x:G),(0:PrueferModel p))=0
        exact Prod.ext x.property.2 (nsmul_zero p)⟩
    apply Infinite.of_injective j
    intro x y h
    exact Subtype.ext (congrArg (fun z : pSocle p (transfiniteFiltration p α : AddSubgroup Q) => (z:Q).1) h)
  let A := AddSubgroup.closure (Set.range a)
  letI : Finite A := p_primary_finite_tuple_closure G p (Fact.out : p.Prime).ne_zero hG n a
  let i : A →+ Q := (AddMonoidHom.inl G (PrueferModel p)).comp A.subtype
  have hi : Function.Injective i := by
    intro x y h
    exact Subtype.ext (congrArg Prod.fst h)
  let e : A ≃+ i.range := AddMonoidHom.ofInjective hi
  letI : Finite i.range := Finite.of_surjective e e.surjective
  have he (x:i.range) : ((x:Q).1:G)=(e.symm x:G) := by
    exact (congrArg (fun z:i.range => (z:Q).1) (e.apply_symm_apply x)).symm
  have hpres : MapCutsExact p e.symm (Ordinal.omega0*γ) := by
    intro x α _
    rw [hd.2.2.1,he]
  have hh := local_cut Q G p hd.2.1 hG i.range A e.symm γ sQ sG
    (fun α _=>hd.2.2.2 α) hpres
  let av : Fin n→A := fun j=>⟨a j,AddSubgroup.subset_closure ⟨j,rfl⟩⟩
  have ht := hh n (fun j=>e (av j))
  change BackAndForth (2*γ) (fun j=>(e.symm (e (av j)):G)) (fun j=>(e (av j):Q)) at ht
  have hei (x:A) : (e x:Q)=((x:G),(0:PrueferModel p)) := rfl
  simpa only [AddEquiv.symm_apply_apply,hei,av] using ht
end LogicLineages.ModelsAlgebra.PGroups
