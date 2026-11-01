module
public import LogicLineages.ModelsAlgebra.PGroups.BoundedReducedProductTargets
public import LogicLineages.ModelsAlgebra.PGroups.FiniteTerminalDeletionProof
public import LogicLineages.ModelsAlgebra.PGroups.FiniteSocleWindowProof
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleProductComparisonProof
public import LogicLineages.ModelsAlgebra.PGroups.BackForth
public import LogicLineages.ModelsAlgebra.PGroups.Infinitary
public import LogicLineages.ModelsAlgebra.PGroups.RawScottRestriction
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth GroupInfinitary

theorem filtration_equiv_cut_mem {G H:Type} [AddCommGroup G] [AddCommGroup H]
    (p:ℕ) (e:G≃+H) (α:Ordinal.{0}) (x:G) :
    e x∈(transfiniteFiltration p α:AddSubgroup H) ↔ x∈(transfiniteFiltration p α:AddSubgroup G) := by
  have hk:e.toAddMonoidHom.ker≤(transfiniteFiltration p α:AddSubgroup G) := by
    rw [e.toAddMonoidHom.ker_eq_bot e.injective]
    exact bot_le
  have hm:=map_transfiniteFiltration_below p e.toAddMonoidHom e.surjective α hk α le_rfl
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

noncomputable def filtrationSocleEquiv {G H:Type} [AddCommGroup G] [AddCommGroup H]
    (p:ℕ) (e:G≃+H) (α:Ordinal.{0}) :
    pSocle p (transfiniteFiltration p α:AddSubgroup G) ≃+
      pSocle p (transfiniteFiltration p α:AddSubgroup H) where
  toFun x:=⟨e x,(filtration_equiv_cut_mem p e α x).mpr x.property.1,by
    have hx:p • (x:G)=0:=x.property.2
    change p • e (x:G)=0
    rw [←map_nsmul,hx,map_zero]⟩
  invFun x:=⟨e.symm x,(filtration_equiv_cut_mem p e.symm α x).mpr x.property.1,by
    have hx:p • (x:H)=0:=x.property.2
    change p • e.symm (x:H)=0
    rw [←map_nsmul,hx,map_zero]⟩
  left_inv x:=Subtype.ext (e.symm_apply_apply x)
  right_inv x:=Subtype.ext (e.apply_symm_apply x)
  map_add' x y:=Subtype.ext (e.map_add x y)

theorem product_cut_socle_finite (R D:Type) [AddCommGroup R] [AddCommGroup D]
    (p:ℕ) [Fact p.Prime] [Finite (pSocle p (⊤:AddSubgroup D))]
    (hR:∀x:R,∃k:ℕ,p^k • x=0) (hD:∀x:D,∃k:ℕ,p^k • x=0) (hd:GroupDivisible D)
    (δ:Ordinal.{0}) [Finite (transfiniteFiltration p δ:AddSubgroup R)] :
    Finite (pSocle p (transfiniteFiltration p δ:AddSubgroup (R×D))) := by
  have hm:=(divisible_product_data R D p hR hD hd).2.1
  let j:pSocle p (transfiniteFiltration p δ:AddSubgroup (R×D))→
      ↥(transfiniteFiltration p δ:AddSubgroup R) × ↥(pSocle p (⊤:AddSubgroup D)) := fun x=>
    (⟨(x:R×D).1,(hm δ _).mp x.property.1⟩,
      ⟨(x:R×D).2,AddSubgroup.mem_top _,by
        have hx:p • (x:R×D)=0:=x.property.2
        exact congrArg Prod.snd hx⟩)
  apply Finite.of_injective j
  intro x y h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun z:↥(transfiniteFiltration p δ:AddSubgroup R) × ↥(pSocle p (⊤:AddSubgroup D))=>(z.1:R)) h)
    (congrArg (fun z:↥(transfiniteFiltration p δ:AddSubgroup R) × ↥(pSocle p (⊤:AddSubgroup D))=>(z.2:D)) h)

private theorem product_cut_socle_infinite (R D:Type) [AddCommGroup R] [AddCommGroup D]
    (p:ℕ) [Fact p.Prime] (hR:∀x:R,∃k:ℕ,p^k • x=0)
    (hD:∀x:D,∃k:ℕ,p^k • x=0) (hd:GroupDivisible D) (δ:Ordinal.{0}) (N:ℕ)
    (hbound:∀x:(transfiniteFiltration p δ:AddSubgroup R),p^N • x=0)
    (hinf:Infinite (transfiniteFiltration p δ:AddSubgroup R)) :
    Infinite (pSocle p (transfiniteFiltration p δ:AddSubgroup (R×D))) := by
  let S:AddSubgroup R:=transfiniteFiltration p δ
  have hS:Infinite (pSocle p S) := by
    apply not_finite_iff_infinite.mp
    intro hfin
    letI:=hfin
    let i:pSocle p (⊤:AddSubgroup S)→pSocle p S:=fun x=>
      ⟨((x:S):R),(x:S).property,congrArg Subtype.val x.property.2⟩
    have hi:Function.Injective i:=by
      intro x y h
      exact Subtype.ext (Subtype.ext (congrArg (fun z:pSocle p S=>(z:R)) h))
    letI:Finite (pSocle p (⊤:AddSubgroup S)):=Finite.of_injective i hi
    letI:Finite (powerTorsion S p N):=finite_socle_power_torsion S p N
    let j:S→powerTorsion S p N:=fun x=>⟨x,hbound x⟩
    have hj:Function.Injective j:=fun _ _ h=>congrArg Subtype.val h
    have hSfin:Finite S:=Finite.of_injective j hj
    exact hinf.false
  letI:=hS
  have hm:=(divisible_product_data R D p hR hD hd).2.1
  let j:pSocle p S→pSocle p (transfiniteFiltration p δ:AddSubgroup (R×D)):=fun x=>
    ⟨((x:R),0),(hm δ _).mpr x.property.1,Prod.ext x.property.2 (nsmul_zero p)⟩
  apply Infinite.of_injective j
  intro x y h
  exact Subtype.ext (congrArg (fun z:pSocle p (transfiniteFiltration p δ:AddSubgroup (R×D))=>(z:R×D).1) h)

theorem bounded_reduced_product_competitor : Targets.boundedReducedProductCompetitor := by
  classical
  intro R D _ _ _ _ p _ _ hR hD hr hd γ N hbound hinf n a
  let δ:=Ordinal.omega0*γ
  obtain ⟨T,_,hfinite,_,hbf⟩ := finite_terminal_deletion R p hR hr γ N hbound hinf n (fun i=>(a i).1)
  let Q:=R⧸T
  let q:=QuotientAddGroup.mk' T
  letI:Countable Q:=(QuotientAddGroup.mk'_surjective T).countable
  letI:Finite (transfiniteFiltration p δ:AddSubgroup Q):=hfinite
  have hQ:=p_primary_quotient R p T hR
  letI:Infinite (pSocle p (transfiniteFiltration p δ:AddSubgroup (R×D))):=
    product_cut_socle_infinite R D p hR hD hd δ N hbound hinf
  letI:Finite (pSocle p (transfiniteFiltration p δ:AddSubgroup (Q×D))):=
    product_cut_socle_finite Q D p hQ hD hd δ
  have hne:¬Nonempty ((R×D)≃+(Q×D)):=by
    rintro ⟨e⟩
    let j:=filtrationSocleEquiv p e δ
    have hfinite:Finite (pSocle p (transfiniteFiltration p δ:AddSubgroup (R×D))):=
      Finite.of_injective j j.injective
    letI:=hfinite
    exact not_finite (pSocle p (transfiniteFiltration p δ:AddSubgroup (R×D)))
  refine ⟨Q×D,inferInstance,inferInstance,(divisible_product_data Q D p hQ hD hd).1,hne,
    (fun i=>(q (a i).1,(a i).2)),?_⟩
  have hh:=finite_product_preservation (2*γ+1) R D Q D n (fun i=>(a i).1) (fun i=>(a i).2)
    (fun i=>q (a i).1) (fun i=>(a i).2) hbf (comparison_reflexive (2*γ+1) D n (fun i=>(a i).2))
  simpa only [Prod.mk.eta] using hh

theorem bounded_reduced_product_no_even_raw_sigma : Targets.boundedReducedProductNoEvenRawSigma := by
  classical
  intro R D _ _ _ _ p _ _ hR hD hr hd γ N hbound hinf φ hc hsRaw
  have hs:=raw_scott_restriction (R×D) φ hsRaw
  generalize hlevel:2*γ+2=α at hc
  cases hc with
  | qf side q=>exact ((by positivity:(2*γ+2:Ordinal)≠0) hlevel).elim
  | sigma hpos s m matrix β lower rank=>
    subst α
    obtain ⟨j,d,hmat⟩:=hs.1
    obtain ⟨H,inst,hct,_,hne,b,hbf⟩:=bounded_reduced_product_competitor R D p hR hD hr hd γ N hbound hinf
      (0+m j) (append Fin.elim0 d)
    letI:=inst
    letI:Countable H:=hct
    have hβ:β j≤2*γ+1:=Order.le_of_lt_succ (by
      simpa only [Order.succ_eq_add_one,add_assoc,one_add_one_eq_two] using lower j)
    have hb:=back_forth_monotone (2*γ+1) (β j) hβ (R×D) H (0+m j) _ _ hbf
    have ht:=(truth_transfer (β j) (R×D) H (0+m j) _ _ hb).1 (matrix j) (rank j) hmat
    let c:Fin (m j)→H:=fun i=>b (Fin.natAdd 0 i)
    have he:append (Fin.elim0:Fin 0→H) c=b:=by
      funext i
      induction i using Fin.addCases with
      | left i=>exact i.elim0
      | right i=>
        change Fin.addCases Fin.elim0 c (Fin.natAdd 0 i)=b (Fin.natAdd 0 i)
        rw [Fin.addCases_right]
    exact hne (hs.2 H ⟨j,c,by rw [he]; exact ht⟩)
end LogicLineages.ModelsAlgebra.PGroups
