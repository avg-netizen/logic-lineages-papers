module
public import LogicLineages.ModelsAlgebra.PGroups.InfiniteSocleOddTargets
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleProductComparisonProof
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleNonisoProof
public import LogicLineages.ModelsAlgebra.PGroups.FiniteDivisibleImageProof
public import LogicLineages.ModelsAlgebra.PGroups.PrueferEnlargementProof
public import LogicLineages.ModelsAlgebra.PGroups.Infinitary
public import LogicLineages.ModelsAlgebra.PGroups.RawScottRestriction
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth GroupInfinitary

private theorem reservoir_socles (R D : Type) [AddCommGroup R] [AddCommGroup D]
    (p : ℕ) (δ : Ordinal.{0}) (sR : SoclesInfiniteBelow p R δ)
    (hm : ∀ (α:Ordinal.{0}) (x:R×D), x∈transfiniteFiltration p α ↔ x.1∈transfiniteFiltration p α) :
    SoclesInfiniteBelow p (R×D) δ := by
  intro α hα
  letI := sR α hα
  let j : pSocle p (transfiniteFiltration p α : AddSubgroup R) →
      pSocle p (transfiniteFiltration p α : AddSubgroup (R×D)) := fun x =>
    ⟨((x:R),0),(hm α _).mpr x.property.1,by
      change p • ((x:R),(0:D))=0
      exact Prod.ext x.property.2 (nsmul_zero p)⟩
  apply Infinite.of_injective j
  intro x y h
  exact Subtype.ext (congrArg (fun z : pSocle p (transfiniteFiltration p α : AddSubgroup (R×D)) => (z:R×D).1) h)

private theorem divisible_socles (R E : Type) [AddCommGroup R] [AddCommGroup E]
    (p : ℕ) [Infinite (pSocle p (⊤:AddSubgroup E))]
    (hm : ∀ (α:Ordinal.{0}) (x:R×E), x∈transfiniteFiltration p α ↔ x.1∈transfiniteFiltration p α)
    (δ:Ordinal.{0}) : SoclesInfiniteBelow p (R×E) δ := by
  intro α _
  let j : pSocle p (⊤:AddSubgroup E) →
      pSocle p (transfiniteFiltration p α : AddSubgroup (R×E)) := fun x =>
    ⟨(0,(x:E)),(hm α _).mpr (AddSubgroup.zero_mem _),by
      change p • ((0:R),(x:E))=0
      exact Prod.ext (nsmul_zero p) x.property.2⟩
  apply Infinite.of_injective j
  intro x y h
  exact Subtype.ext (congrArg (fun z : pSocle p (transfiniteFiltration p α : AddSubgroup (R×E)) => (z:R×E).2) h)

theorem infinite_socle_odd_product_comparison : Targets.infiniteSocleOddProductComparison := by
  intro R D E _ _ _ _ _ _ p _ _ hR hD hE hr hd he γ hl B C _ f hf
  have dD := divisible_product_data R D p hR hD hd
  have dE := divisible_product_data R E p hR hE he
  have sR : SoclesInfiniteBelow p R (Ordinal.omega0*γ) := by
    by_cases hz:γ=0
    · intro α hα
      simp only [hz,mul_zero,not_lt_zero] at hα
    · exact reduced_long_limit_infinite_socles R p hR hr _
        (Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 (lt_of_le_of_ne zero_le (Ne.symm hz))) hl
  apply (local_socle_back_forth (R×D) (R×E) p dD.1 dE.1 B C f).1 γ
    (reservoir_socles R D p _ sR dD.2.1)
    (divisible_socles R E p dE.2.1 _)
  · intro α _
    exact (dD.2.2 α).trans (dE.2.2 α).symm
  · intro x α _
    rw [dE.2.1,dD.2.1,hf]
  · intro x α _ hx
    exact (dE.2.1 α _).mpr (hf x ▸ (dD.2.1 α _).mp hx)

private theorem hom_tuple_odd_comparison (R D E : Type) [AddCommGroup R] [AddCommGroup D]
    [AddCommGroup E] [Countable R] [Countable D] [Countable E] (p:ℕ) [Fact p.Prime]
    [Infinite (pSocle p (⊤:AddSubgroup D))]
    (hR:∀x:R,∃k:ℕ,p^k • x=0) (hD:∀x:D,∃k:ℕ,p^k • x=0)
    (hE:∀x:E,∃k:ℕ,p^k • x=0) (hr:IsReducedAddGroup R)
    (hd:GroupDivisible D) (he:GroupDivisible E) (γ:Ordinal.{0})
    (hl:StagesNonzeroBelow p R (Ordinal.omega0*γ)) (n:ℕ) (a:Fin n→R×D)
    (S:AddSubgroup D) (f:D→+E) (hf:Function.Injective (f.comp S.subtype))
    (ha:∀i,(a i).2∈S) : BackAndForth (2*γ+1) a (fun i=>((a i).1,f (a i).2)) := by
  classical
  let B := AddSubgroup.closure (Set.range a)
  let q : R×D →+ R×E := (AddMonoidHom.id R).prodMap f
  let j : B →+ R×E := q.comp B.subtype
  have hB : B ≤ S.comap (AddMonoidHom.snd R D) := by
    apply (AddSubgroup.closure_le _).mpr
    rintro x ⟨i,rfl⟩
    exact ha i
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    have hfirst : (x:R×D).1 = (y:R×D).1 := by
      have hh : (j x).1 = (j y).1 := congrArg (fun z : R×E => z.1) h
      exact hh
    apply Prod.ext hfirst
    have heq := congrArg Prod.snd h
    have hh := hf (a₁:=⟨(x:R×D).2,hB x.property⟩)
      (a₂:=⟨(y:R×D).2,hB y.property⟩) heq
    exact congrArg Subtype.val hh
  let e : B ≃+ j.range := AddMonoidHom.ofInjective hj
  letI : Finite B := p_primary_finite_tuple_closure (R×D) p (Fact.out : p.Prime).ne_zero
    (divisible_product_data R D p hR hD hd).1 n a
  letI : Finite j.range := Finite.of_surjective e e.surjective
  have hcoord (x:j.range) : (e.symm x:R×D).1=(x:R×E).1 := by
    exact congrArg (fun z:j.range => (z:R×E).1) (e.apply_symm_apply x)
  have hh := infinite_socle_odd_product_comparison R E D p hR hE hD hr he hd γ hl j.range B e.symm hcoord
  let av : Fin n→B := fun i=>⟨a i,AddSubgroup.subset_closure ⟨i,rfl⟩⟩
  have ht := hh n (fun i=>e (av i))
  change BackAndForth (2*γ+1) (fun i=>(e.symm (e (av i)):R×D)) (fun i=>(e (av i):R×E)) at ht
  have hei (x:B) : (e x:R×E)=((x:R×D).1,f (x:R×D).2) := rfl
  simpa only [AddEquiv.symm_apply_apply,hei,av] using ht

theorem infinite_socle_odd_product_competitor : Targets.infiniteSocleOddProductCompetitor := by
  classical
  intro R D _ _ _ _ p _ _ hR hD hr hd γ hl n a
  letI : Countable (PrueferModel p) := pruefer_model_countable p
  let S := AddSubgroup.closure (Set.range (fun i=>(a i).2))
  letI : Finite S := p_primary_finite_tuple_closure D p (Fact.out : p.Prime).ne_zero hD n (fun i=>(a i).2)
  obtain ⟨m,f,hf,he,hfin,_⟩ := finite_divisible_image p D hD hd S
  let E := f.range
  letI : Finite (pSocle p (⊤:AddSubgroup E)) := hfin
  let g : D →+ E := f.codRestrict f.range (fun x=>⟨x,rfl⟩)
  have hE : ∀ x:E,∃k:ℕ,p^k • x=0 := by
    intro x
    obtain ⟨y,hy⟩ := x.property
    obtain ⟨k,hk⟩ := hD y
    refine ⟨k,Subtype.ext ?_⟩
    change p^k • (x:Fin m→PrueferModel p)=0
    rw [←hy,←map_nsmul,hk,map_zero]
  have hg : Function.Injective (g.comp S.subtype) := by
    intro x y h
    exact hf (congrArg (fun z:E => (z:Fin m→PrueferModel p)) h)
  refine ⟨R×E,inferInstance,inferInstance,(divisible_product_data R E p hR hE he).1,
    divisible_infinite_finite_noniso R R D E p hr hr hd he,fun i=>((a i).1,g (a i).2),?_⟩
  exact hom_tuple_odd_comparison R D E p hR hD hE hr hd he γ hl n a S g hg
    (fun i=>AddSubgroup.subset_closure ⟨i,rfl⟩)

theorem infinite_socle_no_even_raw_sigma : Targets.infiniteSocleNoEvenRawSigma := by
  classical
  intro R D _ _ _ _ p _ _ hR hD hr hd γ _ hl φ hc hsRaw
  have hs := raw_scott_restriction (R×D) φ hsRaw
  generalize hlevel : 2*γ+2=α at hc
  cases hc with
  | qf side q => exact ((by positivity : (2*γ+2:Ordinal)≠0) hlevel).elim
  | sigma hpos s m matrix β lower rank =>
    subst α
    obtain ⟨j,d,hmat⟩ := hs.1
    obtain ⟨H,inst,hct,_,hne,b,hbf⟩ := infinite_socle_odd_product_competitor R D p hR hD hr hd γ hl
      (0+m j) (append Fin.elim0 d)
    letI := inst
    letI : Countable H := hct
    have hβ : β j≤2*γ+1 := Order.le_of_lt_succ (by
      simpa only [Order.succ_eq_add_one,add_assoc,one_add_one_eq_two] using lower j)
    have hb := back_forth_monotone (2*γ+1) (β j) hβ (R×D) H (0+m j) _ _ hbf
    have ht := (truth_transfer (β j) (R×D) H (0+m j) _ _ hb).1 (matrix j) (rank j) hmat
    let c : Fin (m j) → H := fun i=>b (Fin.natAdd 0 i)
    have he : append (Fin.elim0 : Fin 0 → H) c = b := by
      funext i
      induction i using Fin.addCases with
      | left i => exact i.elim0
      | right i =>
        change Fin.addCases Fin.elim0 c (Fin.natAdd 0 i) = b (Fin.natAdd 0 i)
        rw [Fin.addCases_right]
    exact hne (hs.2 H ⟨j,c,by rw [he]; exact ht⟩)
end LogicLineages.ModelsAlgebra.PGroups
