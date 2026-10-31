module
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleCompetitorTargets
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleProductComparisonProof
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleNonisoProof
public import LogicLineages.ModelsAlgebra.PGroups.FiniteDivisibleImageProof
public import LogicLineages.ModelsAlgebra.PGroups.PrueferEnlargementProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth

private theorem hom_tuple_comparison (R D E : Type) [AddCommGroup R] [AddCommGroup D]
    [AddCommGroup E] [Countable R] [Countable D] [Countable E] (p:ℕ) [Fact p.Prime]
    (hR:∀x:R,∃k:ℕ,p^k • x=0) (hD:∀x:D,∃k:ℕ,p^k • x=0)
    (hE:∀x:E,∃k:ℕ,p^k • x=0) (hr:IsReducedAddGroup R)
    (hd:GroupDivisible D) (he:GroupDivisible E) (γ:Ordinal.{0})
    (hl:StagesNonzeroBelow p R (Ordinal.omega0*γ)) (n:ℕ) (a:Fin n→R×D)
    (S:AddSubgroup D) (f:D→+E) (hf:Function.Injective (f.comp S.subtype))
    (ha:∀i,(a i).2∈S) : BackAndForth (2*γ) a (fun i=>((a i).1,f (a i).2)) := by
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
  have hh := divisible_product_comparison R E D p hR hE hD hr he hd γ hl j.range B e.symm hcoord
  let av : Fin n→B := fun i=>⟨a i,AddSubgroup.subset_closure ⟨i,rfl⟩⟩
  have ht := hh n (fun i=>e (av i))
  change BackAndForth (2*γ) (fun i=>(e.symm (e (av i)):R×D)) (fun i=>(e (av i):R×E)) at ht
  have hei (x:B) : (e x:R×E)=((x:R×D).1,f (x:R×D).2) := rfl
  simpa only [AddEquiv.symm_apply_apply,hei,av] using ht

theorem divisible_product_competitor : Targets.divisibleProductCompetitor := by
  classical
  intro R D _ _ _ _ p _ hR hD hr hd γ hl n a
  letI : Countable (PrueferModel p) := pruefer_model_countable p
  rcases finite_or_infinite (pSocle p (⊤ : AddSubgroup D)) with hfin | hinf
  · letI := hfin
    let E := D×PrueferModel p
    have hE := (pruefer_enlargement_data D p hD).2.1
    have he : GroupDivisible E := by
      intro k hk x
      obtain ⟨y,hy⟩ := hd k hk x.1
      obtain ⟨z,hz⟩ := (genuine_pruefer_model p).2.1 k hk x.2
      exact ⟨(y,z),Prod.ext hy hz⟩
    let f : D →+ E := AddMonoidHom.inl D (PrueferModel p)
    have hf : Function.Injective (f.comp (⊤ : AddSubgroup D).subtype) := by
      intro x y h
      exact Subtype.ext (congrArg Prod.fst h)
    refine ⟨R×E,inferInstance,inferInstance,(divisible_product_data R E p hR hE he).1,
      divisible_finite_pruefer_noniso p R D hr hd,fun i=>((a i).1,f (a i).2),?_⟩
    exact hom_tuple_comparison R D E p hR hD hE hr hd he γ hl n a ⊤ f hf (fun _=>AddSubgroup.mem_top _)
  · letI := hinf
    let S := AddSubgroup.closure (Set.range (fun i=>(a i).2))
    letI : Finite S := p_primary_finite_tuple_closure D p (Fact.out : p.Prime).ne_zero hD n (fun i=>(a i).2)
    obtain ⟨m,f,hf,he,hfin,_⟩ := finite_divisible_image p D hD hd S
    let E := f.range
    letI : Finite (pSocle p (⊤ : AddSubgroup E)) := hfin
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
    exact hom_tuple_comparison R D E p hR hD hE hr hd he γ hl n a S g hg
      (fun i=>AddSubgroup.subset_closure ⟨i,rfl⟩)
end LogicLineages.ModelsAlgebra.PGroups
