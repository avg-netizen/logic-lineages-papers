module
public import LogicLineages.ModelsAlgebra.PGroups.CountableHomogeneityTargets
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleHomogeneityProof
public import LogicLineages.ModelsAlgebra.PGroups.CountableUlmProof
public import LogicLineages.ModelsAlgebra.PGroups.CountableReducedZeroProof
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleSplittingProof
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleProductComparisonProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

private theorem equiv_stage_membership {G H:Type} [AddCommGroup G] [AddCommGroup H]
    (p:ℕ) (e:G≃+H) (α:Ordinal.{0}) (x:G) :
    e x ∈ (transfiniteFiltration p α:AddSubgroup H) ↔
      x ∈ (transfiniteFiltration p α:AddSubgroup G) := by
  have hk : e.toAddMonoidHom.ker ≤ (transfiniteFiltration p α:AddSubgroup G) := by
    rw [e.toAddMonoidHom.ker_eq_bot e.injective]
    exact bot_le
  have hm := map_transfiniteFiltration_below p e.toAddMonoidHom e.surjective α hk α le_rfl
  constructor
  · intro hx
    have hmap : e x ∈ (transfiniteFiltration p α:AddSubgroup G).map e.toAddMonoidHom := by
      rw [hm]
      exact hx
    obtain ⟨y,hy,he⟩ := hmap
    exact (e.injective he) ▸ hy
  · intro hx
    rw [←hm]
    exact ⟨x,hx,rfl⟩

private noncomputable def equalKernelRangeEquiv {A R S:Type}
    [AddCommGroup A] [AddCommGroup R] [AddCommGroup S]
    (j:A→+R) (k:A→+S) (h:j.ker=k.ker) : j.range≃+k.range :=
  (QuotientAddGroup.quotientKerEquivRange j).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq h).trans
      (QuotientAddGroup.quotientKerEquivRange k))

private theorem equalKernelRangeEquiv_apply {A R S:Type}
    [AddCommGroup A] [AddCommGroup R] [AddCommGroup S]
    (j:A→+R) (k:A→+S) (h:j.ker=k.ker) (a:A) :
    equalKernelRangeEquiv j k h (j.rangeRestrict a)=k.rangeRestrict a := by
  have hj : j.rangeRestrict a=
      (QuotientAddGroup.quotientKerEquivRange j) (QuotientAddGroup.mk a) := rfl
  unfold equalKernelRangeEquiv
  rw [hj]
  change (QuotientAddGroup.quotientKerEquivRange k)
    ((QuotientAddGroup.quotientAddEquivOfEq h)
      ((QuotientAddGroup.quotientKerEquivRange j).symm
        ((QuotientAddGroup.quotientKerEquivRange j) (QuotientAddGroup.mk a)))) = _
  rw [AddEquiv.symm_apply_apply,QuotientAddGroup.quotientAddEquivOfEq_mk]
  rfl

private theorem product_projection_kernels (R D:Type) [AddCommGroup R] [AddCommGroup D]
    (p:ℕ) [Fact p.Prime] (hR:∀x:R,∃k:ℕ,p^k • x=0)
    (hD:∀x:D,∃k:ℕ,p^k • x=0) (hd:GroupDivisible D)
    (δ:Ordinal.{0}) (hz:(transfiniteFiltration p δ:AddSubgroup R)=⊥)
    (f:FiniteHeightIso p (R×D) (R×D)) :
    ((AddMonoidHom.fst R D).comp f.domain.subtype).ker =
      ((AddMonoidHom.fst R D).comp
        (f.codomain.subtype.comp f.equiv.toAddMonoidHom)).ker := by
  obtain ⟨_,hmem,_⟩ := divisible_product_data R D p hR hD hd
  apply AddSubgroup.ext
  intro x
  change ((x:R×D).1=0) ↔ ((f.equiv x:R×D).1=0)
  have hB : ((x:R×D).1=0) ↔ (x:R×D)∈transfiniteFiltration p δ := by
    rw [hmem δ (x:R×D),hz,AddSubgroup.mem_bot]
  have hC : ((f.equiv x:R×D).1=0) ↔ (f.equiv x:R×D)∈transfiniteFiltration p δ := by
    rw [hmem δ (f.equiv x:R×D),hz,AddSubgroup.mem_bot]
  exact hB.trans ((f.preserves x δ).symm.trans hC.symm)

private theorem reduced_projection_automorphism (R D:Type)
    [AddCommGroup R] [AddCommGroup D] [Countable R]
    (p:ℕ) [Fact p.Prime] (hR:∀x:R,∃k:ℕ,p^k • x=0)
    (hD:∀x:D,∃k:ℕ,p^k • x=0) (hd:GroupDivisible D)
    (δ:Ordinal.{0}) (hδ:Order.IsSuccLimit δ)
    (hz:(transfiniteFiltration p δ:AddSubgroup R)=⊥)
    (f:FiniteHeightIso p (R×D) (R×D)) :
    ∃ e:R≃+R, ∀x:f.domain, e (x:R×D).1=(f.equiv x:R×D).1 := by
  classical
  letI : Finite f.domain := f.finite_domain
  let j : f.domain→+R := (AddMonoidHom.fst R D).comp f.domain.subtype
  let k : f.domain→+R := (AddMonoidHom.fst R D).comp
    (f.codomain.subtype.comp f.equiv.toAddMonoidHom)
  have hker : j.ker=k.ker := product_projection_kernels R D p hR hD hd δ hz f
  let a : j.range≃+k.range := equalKernelRangeEquiv j k hker
  obtain ⟨_,hmem,_⟩ := divisible_product_data R D p hR hD hd
  let F : FiniteHeightIso p R R :=
    { domain := j.range
      codomain := k.range
      finite_domain := Finite.of_surjective j.rangeRestrict (by
        intro x
        obtain ⟨b,hb⟩ := x.property
        exact ⟨b,Subtype.ext hb⟩)
      equiv := a
      preserves := by
        intro x α
        obtain ⟨b,hb⟩ := x.property
        have hx : j.rangeRestrict b=x := Subtype.ext hb
        rw [←hx,equalKernelRangeEquiv_apply]
        exact (hmem α (f.equiv b:R×D)).symm.trans
          ((f.preserves b α).trans (hmem α (b:R×D))) }
  obtain ⟨e,he,_⟩ := countable_ulm_extends_at_zero_cut R R p hR hR δ hδ hz hz
    (fun _ _=>rfl) F
  refine ⟨e,?_⟩
  intro b
  exact (he (j.rangeRestrict b)).trans
    (congrArg (fun z:k.range=>(z:R)) (equalKernelRangeEquiv_apply j k hker b))

private theorem divisible_projection_automorphism (R D:Type)
    [AddCommGroup R] [AddCommGroup D] [Countable D]
    (p:ℕ) [Fact p.Prime] (hR:∀x:R,∃k:ℕ,p^k • x=0)
    (hD:∀x:D,∃k:ℕ,p^k • x=0) (hd:GroupDivisible D)
    (δ:Ordinal.{0}) (hz:(transfiniteFiltration p δ:AddSubgroup R)=⊥)
    (f:FiniteHeightIso p (R×D) (R×D)) :
    ∃ e:D≃+D, ∀x:f.domain, (x:R×D).1=0 →
      e (x:R×D).2=(f.equiv x:R×D).2 := by
  classical
  letI : Finite f.domain := f.finite_domain
  let B : AddSubgroup D := f.domain.comap (AddMonoidHom.inr R D)
  let i : B→+f.domain :=
    { toFun:=fun x=>⟨(0,(x:D)),x.property⟩
      map_zero':=rfl
      map_add':=fun _ _=>Subtype.ext (Prod.ext (zero_add (0:R)).symm rfl) }
  have hi : Function.Injective i := by
    intro x y h
    exact Subtype.ext (congrArg (fun z:f.domain=>(z:R×D).2) h)
  letI : Finite B := Finite.of_injective i hi
  let h : B→+D := (AddMonoidHom.snd R D).comp
    (f.codomain.subtype.comp (f.equiv.toAddMonoidHom.comp i))
  have hzero (x:B) : (f.equiv (i x):R×D).1=0 := by
    have hk := product_projection_kernels R D p hR hD hd δ hz f
    have hmem : i x∈((AddMonoidHom.fst R D).comp f.domain.subtype).ker := by
      change (0:R)=0
      rfl
    exact (SetLike.ext_iff.mp hk (i x)).mp hmem
  have hh : Function.Injective h := by
    intro x y he
    have hp : (f.equiv (i x):R×D)=(f.equiv (i y):R×D) :=
      Prod.ext ((hzero x).trans (hzero y).symm) he
    have hc : f.equiv (i x)=f.equiv (i y) := Subtype.ext hp
    exact hi (f.equiv.injective hc)
  let eB : B≃+h.range := AddEquiv.ofBijective h.rangeRestrict ⟨by
      intro x y he
      exact hh (congrArg Subtype.val he),by
      intro x
      obtain ⟨b,hb⟩ := x.property
      exact ⟨b,Subtype.ext hb⟩⟩
  obtain ⟨e,he⟩ := primary_divisible_finite_homogeneity D p hD hd B h.range eB
  refine ⟨e,?_⟩
  intro x hx
  let b : B := ⟨(x:R×D).2,by
    change (0,(x:R×D).2)∈f.domain
    have hp : (0,(x:R×D).2)=(x:R×D) := Prod.ext hx.symm rfl
    rw [hp]
    exact x.property⟩
  have hix : i b=x := Subtype.ext (Prod.ext hx.symm rfl)
  have hev := he b
  change e (x:R×D).2=(f.equiv (i b):R×D).2 at hev
  rwa [hix] at hev

private noncomputable def rangeFactor {A R D:Type}
    [AddCommGroup A] [AddCommGroup R] [AddCommGroup D]
    (j:A→+R) (h:A→+D) (hk:j.ker≤h.ker) : j.range→+D :=
  (QuotientAddGroup.lift j.ker h hk).comp
    (QuotientAddGroup.quotientKerEquivRange j).symm.toAddMonoidHom

private theorem rangeFactor_apply {A R D:Type}
    [AddCommGroup A] [AddCommGroup R] [AddCommGroup D]
    (j:A→+R) (h:A→+D) (hk:j.ker≤h.ker) (a:A) :
    rangeFactor j h hk (j.rangeRestrict a)=h a := by
  have hj : j.rangeRestrict a=
      (QuotientAddGroup.quotientKerEquivRange j) (QuotientAddGroup.mk a) := rfl
  rw [hj]
  change (QuotientAddGroup.lift j.ker h hk)
    ((QuotientAddGroup.quotientKerEquivRange j).symm
      ((QuotientAddGroup.quotientKerEquivRange j) (QuotientAddGroup.mk a)))=h a
  rw [AddEquiv.symm_apply_apply]
  rfl

private theorem product_height_automorphism (R D:Type)
    [AddCommGroup R] [AddCommGroup D] [Countable R] [Countable D]
    (p:ℕ) [Fact p.Prime] (hR:∀x:R,∃k:ℕ,p^k • x=0)
    (hD:∀x:D,∃k:ℕ,p^k • x=0) (hd:GroupDivisible D)
    (δ:Ordinal.{0}) (hδ:Order.IsSuccLimit δ)
    (hz:(transfiniteFiltration p δ:AddSubgroup R)=⊥)
    (f:FiniteHeightIso p (R×D) (R×D)) :
    ∃ e:(R×D)≃+(R×D), ∀x:f.domain, e x=(f.equiv x:R×D) := by
  classical
  obtain ⟨r,hr⟩ := reduced_projection_automorphism R D p hR hD hd δ hδ hz f
  obtain ⟨d,hdmap⟩ := divisible_projection_automorphism R D p hR hD hd δ hz f
  let j : f.domain→+R := (AddMonoidHom.fst R D).comp f.domain.subtype
  let h : f.domain→+D :=
    (AddMonoidHom.snd R D).comp (f.codomain.subtype.comp f.equiv.toAddMonoidHom) -
      d.toAddMonoidHom.comp ((AddMonoidHom.snd R D).comp f.domain.subtype)
  have hker : j.ker≤h.ker := by
    intro x hx
    have hx0 : (x:R×D).1=0 := hx
    change (f.equiv x:R×D).2-d (x:R×D).2=0
    rw [hdmap x hx0,sub_self]
  let m : j.range→+D := rangeFactor j h hker
  obtain ⟨H,hH⟩ := divisible_hom_extension R D hd j.range m
  have hHpoint (x:f.domain) : H (x:R×D).1=h x :=
    (hH (j.rangeRestrict x)).trans (rangeFactor_apply j h hker x)
  let e : (R×D)≃+(R×D) :=
    { toFun:=fun x=>(r x.1,d x.2+H x.1)
      invFun:=fun y=>(r.symm y.1,d.symm (y.2-H (r.symm y.1)))
      left_inv:=by
        intro x
        apply Prod.ext
        · exact r.symm_apply_apply x.1
        · change d.symm ((d x.2+H x.1)-H (r.symm (r x.1)))=x.2
          rw [r.symm_apply_apply,add_sub_cancel_right,d.symm_apply_apply]
      right_inv:=by
        intro y
        apply Prod.ext
        · exact r.apply_symm_apply y.1
        · change d (d.symm (y.2-H (r.symm y.1)))+H (r.symm y.1)=y.2
          rw [d.apply_symm_apply,sub_add_cancel]
      map_add':=by
        intro x y
        apply Prod.ext
        · exact r.map_add x.1 y.1
        · change d (x.2+y.2)+H (x.1+y.1)=(d x.2+H x.1)+(d y.2+H y.1)
          rw [map_add,map_add]
          exact add_add_add_comm _ _ _ _ }
  refine ⟨e,?_⟩
  intro x
  apply Prod.ext
  · exact hr x
  · change d (x:R×D).2+H (x:R×D).1=(f.equiv x:R×D).2
    rw [hHpoint]
    change d (x:R×D).2+((f.equiv x:R×D).2-d (x:R×D).2)=(f.equiv x:R×D).2
    rw [add_comm (d (x:R×D).2),sub_add_cancel]

private noncomputable def transportedHeightIso {G P:Type}
    [AddCommGroup G] [AddCommGroup P] (p:ℕ) (e:P≃+G)
    (f:FiniteHeightIso p G G) : FiniteHeightIso p P P := by
  classical
  let i := e.symm.addSubgroupMap f.domain
  let j := e.symm.addSubgroupMap f.codomain
  letI : Finite f.domain := f.finite_domain
  refine
    { domain:=f.domain.map e.symm.toAddMonoidHom
      codomain:=f.codomain.map e.symm.toAddMonoidHom
      finite_domain:=Finite.of_surjective i i.surjective
      equiv:=i.symm.trans (f.equiv.trans j)
      preserves:=?_ }
  intro x α
  have hx : e (x:P)=(i.symm x:G) := by
    have hh := congrArg (fun y:f.domain.map e.symm.toAddMonoidHom=>(y:P))
      (i.apply_symm_apply x)
    change e.symm (i.symm x:G)=(x:P) at hh
    simpa only [e.apply_symm_apply] using (congrArg e hh).symm
  change e.symm (f.equiv (i.symm x):G)∈transfiniteFiltration p α ↔
    (x:P)∈transfiniteFiltration p α
  apply (equiv_stage_membership p e.symm α (f.equiv (i.symm x):G)).trans
  apply (f.preserves (i.symm x) α).trans
  rw [←hx]
  exact equiv_stage_membership p e α (x:P)

private theorem transportedHeightIso_apply {G P:Type}
    [AddCommGroup G] [AddCommGroup P] (p:ℕ) (e:P≃+G)
    (f:FiniteHeightIso p G G) (x:f.domain) :
    ((transportedHeightIso p e f).equiv ((e.symm.addSubgroupMap f.domain) x):P)=
      e.symm (f.equiv x:G) := by
  change e.symm (f.equiv ((e.symm.addSubgroupMap f.domain).symm
    ((e.symm.addSubgroupMap f.domain) x)):G)=_
  rw [AddEquiv.symm_apply_apply]

theorem countable_primary_finite_height_homogeneity :
    Targets.countablePrimaryFiniteHeightHomogeneity := by
  classical
  intro G _ _ p _ hprimary f
  obtain ⟨r,R,_,_,hred,_,_,e,_⟩ := actual_divisible_splitting G
  let D : AddSubgroup G := divisiblePart G
  have hR : ∀x:R,∃k:ℕ,p^k • x=0 := by
    intro x
    obtain ⟨k,hk⟩ := hprimary (x:G)
    exact ⟨k,Subtype.ext hk⟩
  have hD : ∀x:D,∃k:ℕ,p^k • x=0 := by
    intro x
    obtain ⟨k,hk⟩ := hprimary (x:G)
    exact ⟨k,Subtype.ext hk⟩
  have hd : GroupDivisible D := (actual_divisible_part G).1
  obtain ⟨δ,_,hδ,hz⟩ := countable_reduced_zero_limit R p hR hred
  let F := transportedHeightIso p e f
  obtain ⟨u,hu⟩ := product_height_automorphism R D p hR hD hd δ hδ hz F
  refine ⟨e.symm.trans (u.trans e),?_⟩
  intro x
  have hx := congrArg e (hu ((e.symm.addSubgroupMap f.domain) x))
  rw [transportedHeightIso_apply,e.apply_symm_apply] at hx
  exact hx

end LogicLineages.ModelsAlgebra.PGroups
