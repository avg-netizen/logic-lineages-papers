module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteSocleReducedTargets
public import LogicLineages.ModelsAlgebra.PGroups.FiniteOmegaBoundProof
public import LogicLineages.ModelsAlgebra.PGroups.CountableReducedZeroProof
public import LogicLineages.ModelsAlgebra.PGroups.PowerStepSelection
public import LogicLineages.ModelsAlgebra.PGroups.FiniteOrdinalFiltration
public import LogicLineages.ModelsAlgebra.PGroups.UlmFiniteIndependence
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteTail
public import Mathlib.Data.Fintype.Pigeonhole
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

private theorem finite_root_fiber (G : Type) [AddCommGroup G] (p : ℕ)
    [Finite (pSocle p (⊤ : AddSubgroup G))] (x : G) : Finite {y : G // p • y = x} := by
  classical
  by_cases hn : Nonempty {y : G // p • y = x}
  · obtain ⟨y₀⟩ := hn
    let j : {y : G // p • y = x} → pSocle p (⊤ : AddSubgroup G) := fun y =>
      ⟨(y:G)-y₀,AddSubgroup.mem_top _,by
        change p • ((y:G)-(y₀:G)) = 0
        rw [nsmul_sub,y.property,y₀.property,sub_self]⟩
    apply Finite.of_injective j
    intro a b h
    apply Subtype.ext
    simpa only [j,sub_left_inj] using congrArg (fun z : pSocle p (⊤ : AddSubgroup G) => (z:G)) h
  · letI : IsEmpty {y : G // p • y = x} := not_nonempty_iff.mp hn
    infer_instance

private theorem finite_bounded (G : Type) [AddCommGroup G] (p : ℕ)
    [Finite (pSocle p (⊤ : AddSubgroup G))] (N : ℕ) (hb : ∀ x : G, p^N • x = 0) : Finite G := by
  classical
  have hk : ∀ n : ℕ, Finite {x : G // p^n • x = 0} := by
    intro n
    induction n with
    | zero =>
      let f : {x : G // p^0 • x = 0} → PUnit := fun _ => PUnit.unit
      apply Finite.of_injective f
      intro x y _
      apply Subtype.ext
      have hx : (x:G)=0 := by simpa using x.property
      have hy : (y:G)=0 := by simpa using y.property
      exact hx.trans hy.symm
    | succ n ih =>
      letI := ih
      let f : {x : G // p^(n+1) • x = 0} → {x : G // p^n • x = 0} := fun x =>
        ⟨p • (x:G),by simpa only [pow_succ,mul_smul] using x.property⟩
      by_contra hn
      letI : Infinite {x : G // p^(n+1) • x = 0} := not_finite_iff_infinite.mp hn
      obtain ⟨y,hy⟩ := Finite.exists_infinite_fiber f
      letI := hy
      letI := finite_root_fiber G p (y:G)
      let j : (f ⁻¹' {y}) → {x : G // p • x = (y:G)} := fun x =>
        ⟨(x.val:G),congrArg (fun z : {x : G // p^n • x = 0} => (z:G)) x.property⟩
      have hj : Function.Injective j := by
        intro a b h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : {x : G // p • x = (y:G)} => (z:G)) h
      exact (Finite.of_injective j hj).false
  letI := hk N
  exact Finite.of_injective (fun x : G => (⟨x,hb x⟩ : {x : G // p^N • x = 0}))
    (fun x y h => congrArg Subtype.val h)

theorem finite_socle_omega_stable : Targets.finiteSocleOmegaStable := by
  intro G _ p _
  classical
  apply le_antisymm
  · rw [transfiniteFiltration_add_one]
    exact pStep_le p _
  · intro x hx
    have hxn (n : ℕ) : x ∈ (transfiniteFiltration p ((n:Ordinal)+1) : AddSubgroup G) := by
      apply transfiniteFiltration_antitone p ?_ hx
      exact (by simpa only [Nat.cast_add,Nat.cast_one] using (Ordinal.natCast_lt_omega0 (n+1)).le)
    letI := finite_root_fiber G p x
    have hex : ∃ y : {y : G // p • y = x}, ∀ n : ℕ,
        (y:G) ∈ transfiniteFiltration p (n:Ordinal) := by
      by_contra! hn
      choose k hk using hn
      obtain ⟨N,hN⟩ := Finite.exists_le k
      have hm := hxn N
      rw [transfiniteFiltration_add_one] at hm
      obtain ⟨y,hy,hpy⟩ := hm
      let z : {y : G // p • y = x} := ⟨y,hpy⟩
      apply hk z
      exact transfiniteFiltration_antitone p (by exact_mod_cast hN z) hy
    obtain ⟨y,hy⟩ := hex
    have hyω : (y:G) ∈ (transfiniteFiltration p Ordinal.omega0 : AddSubgroup G) := by
      have he := omega_block_filtration G p (0:Ordinal)
      simp only [zero_add] at he
      rw [he]
      exact AddSubgroup.mem_iInf.mpr hy
    rw [transfiniteFiltration_add_one]
    exact ⟨(y:G),hyω,y.property⟩

theorem reduced_finite_socle_finite : Targets.reducedFiniteSocleFinite := by
  intro G _ p _ hG hred hfin
  letI := hfin
  let S := (transfiniteFiltration p (Ordinal.omega0 : Ordinal.{0}) : AddSubgroup G)
  have hprimary : ∀ x : S, ∃ k : ℕ, p^k • x = 0 := by
    intro x
    obtain ⟨k,hk⟩ := hG x
    exact ⟨k,Subtype.ext hk⟩
  have hsurj : ∀ x : S, ∃ y : S, p • y = x := by
    intro x
    have hx : (x:G) ∈ transfiniteFiltration p ((Ordinal.omega0 : Ordinal.{0})+1) := by
      rw [finite_socle_omega_stable G p]
      exact x.property
    rw [transfiniteFiltration_add_one] at hx
    obtain ⟨y,hy,hpy⟩ := hx
    exact ⟨⟨y,hy⟩,Subtype.ext hpy⟩
  have hzero : S = ⊥ := hred S (p_primary_divisible_from_p_surjective S p hprimary hsurj)
  let T := pSocle p (⊤ : AddSubgroup G)
  obtain ⟨N,hN⟩ := finite_omega_block_bound G p T (0:Ordinal)
  have hcut : T ⊓ transfiniteFiltration p (N:Ordinal) = ⊥ := by
    have h := hN N le_rfl
    simp only [zero_add] at h
    change T ⊓ transfiniteFiltration p (N:Ordinal) = T ⊓ S at h
    simpa only [hzero,inf_bot_eq] using h
  have hNzero : (transfiniteFiltration p (N:Ordinal) : AddSubgroup G) = ⊥ := by
    apply le_antisymm
    · by_contra hn
      obtain ⟨x,hx,hxb,hpx⟩ := power_step_selection G p hG ⊥
        (transfiniteFiltration p (N:Ordinal)) bot_le hn
      have hm : x ∈ T ⊓ transfiniteFiltration p (N:Ordinal) :=
        ⟨⟨AddSubgroup.mem_top _,hpx⟩,hx⟩
      rw [hcut] at hm
      exact hxb hm
    · exact bot_le
  apply finite_bounded G p N
  intro x
  have hm : p^N • x ∈ (transfiniteFiltration p (N:Ordinal) : AddSubgroup G) := by
    rw [finite_ordinal_filtration,GroupInfinitary.finite_filtration_multiple_image]
    exact ⟨x,rfl⟩
  rw [hNzero] at hm
  exact hm

private theorem reduced_subgroup (G : Type) [AddCommGroup G] (hG : IsReducedAddGroup G)
    (S : AddSubgroup G) : IsReducedAddGroup S := by
  intro T hT
  let U := T.map S.subtype
  have hU : ∀ n : ℕ, n ≠ 0 → ∀ x : U, ∃ y : U, n • y = x := by
    intro n hn x
    obtain ⟨t,ht,he⟩ := x.property
    obtain ⟨y,hy⟩ := hT n hn ⟨t,ht⟩
    refine ⟨⟨((y:S):G),⟨(y:S),y.property,rfl⟩⟩,Subtype.ext ?_⟩
    exact (congrArg (fun z : T => ((z:S):G)) hy).trans he
  have hz := hG U hU
  apply le_antisymm
  · intro x hx
    have hm : (x:G) ∈ U := ⟨x,hx,rfl⟩
    rw [hz] at hm
    change x = 0
    exact Subtype.ext hm
  · exact bot_le

theorem reduced_long_limit_infinite_socles : Targets.reducedLongLimitInfiniteSocles := by
  intro G _ p _ hG hred δ hδ hlong α hα
  apply not_finite_iff_infinite.mp
  intro hfin
  letI := hfin
  let S := (transfiniteFiltration p α : AddSubgroup G)
  have hprimary : ∀ x : S, ∃ k : ℕ, p^k • x = 0 := by
    intro x
    obtain ⟨k,hk⟩ := hG x
    exact ⟨k,Subtype.ext hk⟩
  let j : pSocle p (⊤ : AddSubgroup S) → pSocle p S := fun x =>
    ⟨((x:S):G),(x:S).property,congrArg Subtype.val x.property.2⟩
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : pSocle p S => (z:G)) h
  letI : Finite (pSocle p (⊤ : AddSubgroup S)) := Finite.of_injective j hj
  letI : Finite S := reduced_finite_socle_finite S p hprimary (reduced_subgroup G hred S) inferInstance
  have hchoose := hprimary
  choose k hk using hchoose
  obtain ⟨N,hN⟩ := Finite.exists_le k
  have hkill : ∀ x : S, p^N • x = 0 := by
    intro x
    obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le (hN x)
    rw [hm,pow_add,mul_nsmul,hk x,nsmul_zero]
  have hzeroS : (transfiniteFiltration p (N:Ordinal) : AddSubgroup S) = ⊥ := by
    rw [finite_ordinal_filtration,GroupInfinitary.finite_filtration_multiple_image]
    apply le_antisymm
    · rintro x ⟨y,rfl⟩
      exact hkill y
    · exact bot_le
  have hzeroG : (transfiniteFiltration p (α+(N:Ordinal)) : AddSubgroup G) = ⊥ := by
    rw [← transfinite_tail_image,hzeroS,AddSubgroup.map_bot]
  have hlt : ∀ n : ℕ, α+(n:Ordinal) < δ := by
    intro n
    induction n with
    | zero => simpa using hα
    | succ n ih =>
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc,Order.succ_eq_add_one] using hδ.succ_lt ih
  exact hlong (α+(N:Ordinal)) (hlt N) hzeroG

end LogicLineages.ModelsAlgebra.PGroups
