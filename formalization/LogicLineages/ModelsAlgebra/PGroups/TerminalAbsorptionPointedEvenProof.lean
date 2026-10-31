module
public import LogicLineages.ModelsAlgebra.PGroups.TerminalAbsorptionPointedEvenTargets
public import LogicLineages.ModelsAlgebra.PGroups.TerminalAbsorptionProof
public import LogicLineages.ModelsAlgebra.PGroups.TerminalTwoEvenProof
public import LogicLineages.ModelsAlgebra.PGroups.TerminalPointedAbsorptionProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth GroupInfinitary
private theorem raise_bound (p k n : ℕ) (hkn : k≤n) (G : Type) [AddCommGroup G]
    (h : ∀ x : G, p^k • x=0) : ∀ x : G, p^n • x=0 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hkn
  intro x
  rw [pow_add,mul_nsmul,h,nsmul_zero]

theorem terminal_absorption_pointed_even : Targets.terminalAbsorptionPointedEven := by
  classical
  intro G _ _ p _ hG rG γ K T N b hsplit hdis hN hRank hT
  let δ : Ordinal := Ordinal.omega0*γ
  let S : AddSubgroup G := transfiniteFiltration p δ
  have hK : K ≤ S := by
    change K ≤ transfiniteFiltration p (Ordinal.omega0*γ)
    rw [hsplit]
    exact le_sup_left
  have hNK : ∀ x : K, p^N • x=0 := by
    intro x
    exact Subtype.ext (congrArg (fun z : S => (z:G)) (hN ⟨x,hK x.property⟩))
  letI : Infinite (finiteFiltration p b : AddSubgroup K) := infinite_ulm_infinite_filtration p K b hRank
  letI : Infinite K := Infinite.of_injective (fun x : (finiteFiltration p b : AddSubgroup K) => (x:K)) Subtype.val_injective
  have hex : ∃ k : ℕ, ∀ x : K, p^k • x=0 := ⟨N,hNK⟩
  let k := Nat.find hex
  have hk : ∀ x : K, p^k • x=0 := Nat.find_spec hex
  have hpos : 0<k := by
    apply Nat.pos_of_ne_zero
    intro hz
    obtain ⟨x,hx⟩ := exists_ne (0:K)
    exact hx (by simpa only [hz,pow_zero,one_nsmul] using hk x)
  have hbk : b<k := by
    by_contra h
    have hz := raise_bound p k b (le_of_not_gt h) K hk
    obtain ⟨x,hx⟩ := exists_ne (0:(finiteFiltration p b : AddSubgroup K))
    obtain ⟨y,hy⟩ := (finite_filtration_multiple_image K p b).le x.property
    change p^b • y = (x:K) at hy
    exact hx (Subtype.ext (hy.symm.trans (hz y)))
  have hTk := raise_bound p (b+1) k (Nat.succ_le_of_lt hbk) T hT
  obtain ⟨es,hes⟩ := subgroup_sum_product G S K T hsplit hdis
  have hSbound : ∀ x : S, p^k • x=0 := by
    intro x
    obtain ⟨⟨a,c⟩,rfl⟩ := es.surjective x
    rw [← map_nsmul]
    have hz : p^k • (a,c) = (0:K×T) := Prod.ext (hk a) (hTk c)
    rw [hz,map_zero]
  have hw : ∃ x : K, p^(k-1) • x≠0 := not_forall.mp (Nat.find_min hex (Nat.sub_lt hpos (by decide : 0<1)))
  have hbase := terminal_deletion_odd G p hG rG γ K T k hsplit hdis hpos hSbound hw
  letI : Countable (G ⧸ T) := (QuotientAddGroup.mk'_surjective T).countable
  have hQ := p_primary_quotient G p T hG
  have rQ := hbase.2.2.1
  have lG : StagesNonzeroBelow p G δ := fun α hα => (hbase.2.2.2.2.1 α (hα.trans_le le_self_add)).1
  have lQ : StagesNonzeroBelow p (G ⧸ T) δ := fun α hα => (hbase.2.2.2.2.1 α (hα.trans_le le_self_add)).2
  obtain ⟨ek,hek⟩ := coherent_terminal_quotient G p δ K T hsplit hdis
  intro n a hA
  let A := AddSubgroup.closure (Set.range a)
  let q := QuotientAddGroup.mk' T
  let qA : A →+ G ⧸ T := q.comp A.subtype
  have hq : Function.Injective qA := by
    intro x y h
    have hinj := retained_sum_quotient_injective G A K T S hsplit hdis hA
    have hh := hinj (a₁ := ⟨(x:G),(le_sup_left : A≤A⊔K) x.property⟩)
      (a₂ := ⟨(y:G),(le_sup_left : A≤A⊔K) y.property⟩) h
    exact Subtype.ext (congrArg (fun z : ↥(A⊔K) => (z:G)) hh)
  let e : A ≃+ qA.range := AddMonoidHom.ofInjective hq
  letI : Finite A := p_primary_finite_tuple_closure G p (Fact.out : p.Prime).ne_zero hG n a
  letI : Finite qA.range := Finite.of_surjective e e.surjective
  have he (x : A) : (e x : G ⧸ T)=q (x:G) := rfl
  have hback (x:qA.range) : q (e.symm x:G)=(x:G ⧸ T) := congrArg Subtype.val (e.apply_symm_apply x)
  have hcuts : MapCutsExact p e.symm δ := by
    intro x β _
    have hh := retained_filtration_reflection G p δ A K T hsplit hdis hA β
      (e.symm x:G) ((le_sup_left : A≤A⊔K) (e.symm x).property)
    rw [hback] at hh
    exact hh.symm
  let U : AddSubgroup (G ⧸ T) := transfiniteFiltration p δ
  let L : AddSubgroup (G ⧸ T) := qA.range ⊓ U
  letI : Finite L := Finite.of_injective (AddSubgroup.inclusion (show L≤qA.range from inf_le_left)) (AddSubgroup.inclusion_injective _)
  letI : Fintype L := Fintype.ofFinite L
  let m := Fintype.card L
  let enum : Fin m → L := (Fintype.equivFin L).symm
  let v : Fin m → qA.range := fun i => ⟨enum i,(enum i).property.1⟩
  let bQ : Fin m → U := fun i => ⟨enum i,(enum i).property.2⟩
  have hdeep (i) : (e.symm (v i):G)∈S := (hcuts (v i) δ le_rfl).mpr (enum i).property.2
  let aS : Fin m → S := fun i => ⟨e.symm (v i),hdeep i⟩
  let cK : Fin m → K := fun i => ⟨e.symm (v i),hA ⟨(e.symm (v i)).property,hdeep i⟩⟩
  have htwo := terminal_pointed_absorption G p S K T N b hsplit hdis hN hRank hT m aS cK (fun _=>rfl)
  have hcK : (fun i=>ek (cK i))=bQ := by
    funext i
    apply Subtype.ext
    exact (hek (cK i)).trans (hback (v i))
  have htwoQ : BackAndForth (2:Ordinal) aS bQ := by
    have hh := (back_forth_isomorphism 2 S K S U (AddEquiv.refl S) ek m aS cK).mp htwo
    simpa only [AddEquiv.refl_apply,hcK] using hh
  have hcomp := terminal_two_even_comparison (G ⧸ T) G p hQ hG rQ rG
    qA.range A e.symm γ lQ lG (fun α hα=>(hbase.1 α hα).symm) hcuts m bQ aS
    (fun i=>(enum i).property.1) (by
      intro x hx hu
      obtain ⟨i,hi⟩ := (Fintype.equivFin L).symm.surjective ⟨x,hx,hu⟩
      exact ⟨i,congrArg Subtype.val hi⟩) (fun _=>rfl) htwoQ
  let av : Fin n → A := fun i=>⟨a i,AddSubgroup.subset_closure ⟨i,rfl⟩⟩
  have hh := hcomp n (fun i=>e (av i))
  change BackAndForth (2*γ+2) (fun i=>(e.symm (e (av i)):G)) (fun i=>(e (av i):G ⧸ T)) at hh
  simpa only [AddEquiv.symm_apply_apply,he,av] using hh
end LogicLineages.ModelsAlgebra.PGroups
