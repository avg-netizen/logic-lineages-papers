module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteSocleWindowTargets
public import LogicLineages.ModelsAlgebra.PGroups.CountableHomogeneityProof
public import LogicLineages.ModelsAlgebra.PGroups.FiniteSocleReducedProof
public import LogicLineages.ModelsAlgebra.PGroups.StableStageProof
public import LogicLineages.ModelsAlgebra.PGroups.FiniteOrdinalFiltration
public import Mathlib.Data.Fintype.Card
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

private theorem finite_p_fiber (G:Type) [AddCommGroup G] (p:ℕ)
    [Finite (pSocle p (⊤:AddSubgroup G))] (x:G) : Finite {y:G // p • y=x} := by
  classical
  by_cases hn:Nonempty {y:G // p • y=x}
  · obtain ⟨y₀⟩ := hn
    let j : {y:G // p • y=x} → pSocle p (⊤:AddSubgroup G) := fun y=>
      ⟨(y:G)-y₀,AddSubgroup.mem_top _,by
        change p • ((y:G)-(y₀:G))=0
        rw [nsmul_sub,y.property,y₀.property,sub_self]⟩
    apply Finite.of_injective j
    intro a b h
    apply Subtype.ext
    simpa only [j,sub_left_inj] using congrArg (fun z:pSocle p (⊤:AddSubgroup G)=>(z:G)) h
  · letI : IsEmpty {y:G // p • y=x} := not_nonempty_iff.mp hn
    infer_instance

theorem finite_socle_power_torsion : Targets.finiteSoclePowerTorsion := by
  classical
  intro G _ p _ n
  have hk : ∀n:ℕ, Finite {x:G // p^n • x=0} := by
    intro n
    induction n with
    | zero =>
      apply Finite.of_injective (fun _:{x:G // p^0 • x=0}=>PUnit.unit)
      intro x y _
      have hx:(x:G)=0 := by simpa only [pow_zero,one_nsmul] using x.property
      have hy:(y:G)=0 := by simpa only [pow_zero,one_nsmul] using y.property
      exact Subtype.ext (hx.trans hy.symm)
    | succ n ih =>
      letI := ih
      let f : {x:G // p^(n+1) • x=0} → {x:G // p^n • x=0} := fun x=>
        ⟨p • (x:G),by simpa only [pow_succ,mul_smul] using x.property⟩
      by_contra hn
      letI : Infinite {x:G // p^(n+1) • x=0} := not_finite_iff_infinite.mp hn
      obtain ⟨y,hy⟩ := Finite.exists_infinite_fiber f
      letI := hy
      letI := finite_p_fiber G p (y:G)
      let j : (f ⁻¹' {y}) → {x:G // p • x=(y:G)} := fun x=>
        ⟨(x.val:G),congrArg (fun z:{x:G // p^n • x=0}=>(z:G)) x.property⟩
      have hj : Function.Injective j := by
        intro a b h
        exact Subtype.ext (Subtype.ext (congrArg (fun z:{x:G // p • x=(y:G)}=>(z:G)) h))
      exact (Finite.of_injective j hj).false
  exact hk n

private theorem equiv_mem {G H:Type} [AddCommGroup G] [AddCommGroup H]
    (p:ℕ) (e:G≃+H) (α:Ordinal.{0}) (x:G) :
    e x∈(transfiniteFiltration p α:AddSubgroup H) ↔ x∈(transfiniteFiltration p α:AddSubgroup G) := by
  have hk:e.toAddMonoidHom.ker≤(transfiniteFiltration p α:AddSubgroup G) := by
    rw [e.toAddMonoidHom.ker_eq_bot e.injective]
    exact bot_le
  have hm := map_transfiniteFiltration_below p e.toAddMonoidHom e.surjective α hk α le_rfl
  constructor
  · intro hx
    have hmap:e x∈(transfiniteFiltration p α:AddSubgroup G).map e.toAddMonoidHom := by
      rw [hm]
      exact hx
    obtain ⟨y,hy,he⟩ := hmap
    exact (e.injective he) ▸ hy
  · intro hx
    rw [←hm]
    exact ⟨x,hx,rfl⟩

theorem finite_socle_finite_stable : Targets.finiteSocleFiniteStable := by
  classical
  intro G _ _ p _ _ hG
  obtain ⟨_,R,_,_,hred,_,_,e,_⟩ := actual_divisible_splitting G
  let D:AddSubgroup G := divisiblePart G
  have hR:∀x:R,∃k:ℕ,p^k • x=0 := by
    intro x
    obtain ⟨k,hk⟩ := hG (x:G)
    exact ⟨k,Subtype.ext hk⟩
  have hD:∀x:D,∃k:ℕ,p^k • x=0 := by
    intro x
    obtain ⟨k,hk⟩ := hG (x:G)
    exact ⟨k,Subtype.ext hk⟩
  let j:pSocle p (⊤:AddSubgroup R)→pSocle p (⊤:AddSubgroup G) := fun x=>
    ⟨((x:R):G),AddSubgroup.mem_top _,congrArg Subtype.val x.property.2⟩
  have hj:Function.Injective j := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z:pSocle p (⊤:AddSubgroup G)=>(z:G)) h))
  letI : Finite (pSocle p (⊤:AddSubgroup R)) := Finite.of_injective j hj
  letI : Finite R := reduced_finite_socle_finite R p hR hred inferInstance
  have hRchoose := hR
  choose k hk using hRchoose
  obtain ⟨N,hN⟩ := Finite.exists_le k
  have hkill:∀x:R,p^N • x=0 := by
    intro x
    obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le (hN x)
    rw [hm,pow_add,mul_nsmul,hk x,nsmul_zero]
  have hz:(transfiniteFiltration p (N:Ordinal.{0}):AddSubgroup R)=⊥ := by
    rw [finite_ordinal_filtration,GroupInfinitary.finite_filtration_multiple_image]
    apply le_antisymm
    · rintro x ⟨y,rfl⟩
      exact hkill y
    · exact bot_le
  have hz':(transfiniteFiltration p ((N:Ordinal.{0})+1):AddSubgroup R)=⊥ :=
    le_antisymm ((transfiniteFiltration_antitone p le_self_add).trans hz.le) bot_le
  have hm := (divisible_product_data R D p hR hD (actual_divisible_part G).1).2.1
  refine ⟨N,?_⟩
  apply AddSubgroup.ext
  intro x
  have h₁ := (equiv_mem p e (N:Ordinal.{0}) (e.symm x)).symm
  have h₂ := equiv_mem p e ((N:Ordinal.{0})+1) (e.symm x)
  simp only [e.apply_symm_apply] at h₁ h₂
  have hmid : (e.symm x)∈(transfiniteFiltration p (N:Ordinal.{0}):AddSubgroup (R×D)) ↔
      (e.symm x)∈(transfiniteFiltration p ((N:Ordinal.{0})+1):AddSubgroup (R×D)) := by
    rw [hm,hm,hz,hz']
  exact h₁.symm.trans (hmid.trans h₂.symm)

private theorem bounded_window_forward (G:Type) [AddCommGroup G] (p N t k:ℕ)
    (hk:k≤N) (u:powerTorsion G p (N+t)≃+powerTorsion G p (N+t))
    (x:powerTorsion G p (N+t)) (hxt:p^t • (x:G)=0)
    (hx:(x:G)∈(transfiniteFiltration p (k:Ordinal.{0}):AddSubgroup G)) :
    (u x:G)∈(transfiniteFiltration p (k:Ordinal.{0}):AddSubgroup G) := by
  rw [finite_ordinal_filtration,GroupInfinitary.finite_filtration_multiple_image] at hx ⊢
  obtain ⟨y,hy⟩ := hx
  change p^k • y=(x:G) at hy
  have hy0:p^(t+k) • y=0 := by
    rw [Nat.add_comm t k,pow_add,mul_nsmul,hy,hxt]
  have hyK:y∈powerTorsion G p (N+t) := by
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le (show t+k≤N+t by omega)
    change p^(N+t) • y=0
    rw [hd,pow_add,mul_nsmul,hy0,nsmul_zero]
  let z:powerTorsion G p (N+t) := ⟨y,hyK⟩
  have hz:p^k • z=x := Subtype.ext hy
  refine ⟨(u z:G),?_⟩
  have hu : p^k • u z=u x := by simpa only [map_nsmul] using congrArg u hz
  change p^k • (u z:G)=(u x:G)
  exact congrArg (fun z:powerTorsion G p (N+t)=>(z:G)) hu

private theorem window_full_height (G:Type) [AddCommGroup G] (p:ℕ) [Fact p.Prime]
    (hG:∀x:G,∃k:ℕ,p^k • x=0) (N t:ℕ) (hs:StableAt p G (N:Ordinal.{0}))
    (u:powerTorsion G p (N+t)≃+powerTorsion G p (N+t))
    (x:powerTorsion G p (N+t)) (hxt:p^t • (x:G)=0) :
    ∀α:Ordinal.{0}, (u x:G)∈(transfiniteFiltration p α:AddSubgroup G) ↔
      (x:G)∈(transfiniteFiltration p α:AddSubgroup G) := by
  have huxt:p^t • (u x:G)=0 := by
    have hx:p^t • x=0 := Subtype.ext hxt
    have hu:p^t • u x=0 := by rw [←map_nsmul,hx,map_zero]
    exact congrArg (fun z:powerTorsion G p (N+t)=>(z:G)) hu
  have hfinite:∀k:ℕ,k≤N→((u x:G)∈(transfiniteFiltration p (k:Ordinal.{0}):AddSubgroup G) ↔
      (x:G)∈(transfiniteFiltration p (k:Ordinal.{0}):AddSubgroup G)) := by
    intro k hk
    constructor
    · intro h
      simpa only [u.symm_apply_apply] using bounded_window_forward G p N t k hk u.symm (u x) huxt h
    · exact bounded_window_forward G p N t k hk u x hxt
  have hstable := primary_stable_stage G p hG (N:Ordinal.{0}) hs
  intro α
  by_cases hα:α<(N:Ordinal.{0})
  · obtain ⟨k,rfl⟩ := Ordinal.lt_omega0.mp (hα.trans (Ordinal.natCast_lt_omega0 N))
    exact hfinite k (by exact_mod_cast hα.le)
  · have hαN:(N:Ordinal.{0})≤α := le_of_not_gt hα
    have he:(transfiniteFiltration p α:AddSubgroup G)=transfiniteFiltration p (N:Ordinal.{0}) :=
      (hstable.2.2 α hαN).1.trans hstable.2.1.symm
    rw [he]
    exact hfinite N le_rfl

theorem finite_socle_embedding_window : Targets.finiteSocleEmbeddingWindow := by
  classical
  intro G _ _ p _ _ hG A _
  obtain ⟨N,hN⟩ := finite_socle_finite_stable G p hG
  choose k hk using fun x:A=>hG (x:G)
  obtain ⟨t,ht⟩ := Finite.exists_le k
  have hkill:∀x:A,p^t • (x:G)=0 := by
    intro x
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le (ht x)
    rw [hd,pow_add,mul_nsmul,hk x,nsmul_zero]
  let B:=powerTorsion G p (N+t)
  letI:Finite B := finite_socle_power_torsion G p (N+t)
  have hAB:A≤B := by
    intro x hx
    change p^(N+t) • x=0
    rw [Nat.add_comm N t,pow_add,mul_nsmul,hkill ⟨x,hx⟩,nsmul_zero]
  refine ⟨B,inferInstance,hAB,?_⟩
  intro f hf
  let j:B→+B := f.codRestrict B (fun x=>by
    change p^(N+t) • f x=0
    rw [←map_nsmul]
    have hx:p^(N+t) • x=0 := Subtype.ext x.property
    rw [hx,map_zero])
  have hj:Function.Injective j := by
    intro x y h
    exact hf (congrArg (fun z:B=>(z:G)) h)
  let u:B≃+B := AddEquiv.ofBijective j ⟨hj,Finite.surjective_of_injective hj⟩
  let a:A→+G := f.comp (AddSubgroup.inclusion hAB)
  have ha:Function.Injective a := hf.comp (AddSubgroup.inclusion_injective hAB)
  let e:A≃+a.range := AddMonoidHom.ofInjective ha
  let F:FiniteHeightIso p G G :=
    { domain:=A
      codomain:=a.range
      finite_domain:=inferInstance
      equiv:=e
      preserves:=by
        intro x α
        change f ⟨(x:G),hAB x.property⟩∈transfiniteFiltration p α ↔ (x:G)∈transfiniteFiltration p α
        exact window_full_height G p hG N t hN u ⟨(x:G),hAB x.property⟩ (hkill x) α }
  obtain ⟨v,hv⟩ := countable_primary_finite_height_homogeneity G p hG F
  exact ⟨v,hv⟩
end LogicLineages.ModelsAlgebra.PGroups
