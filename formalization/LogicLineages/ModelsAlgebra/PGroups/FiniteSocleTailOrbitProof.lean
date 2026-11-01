module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteSocleTailTargets
public import LogicLineages.ModelsAlgebra.PGroups.PointedTableProof
public import LogicLineages.ModelsAlgebra.PGroups.TupleOrbitProof
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteRelativizationProof
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteTail
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary GroupBackAndForth
private noncomputable def sigmaList {n:ℕ} (fs:List (Formula n)) : Formula n :=
  fs.foldr sigmaTwoConjunction (sigmaQF (.equal .zero .zero))

private theorem sigma_list_exact (α:Ordinal.{0}) (htwo:2≤α) (n:ℕ) (fs:List (Formula n)) :
    (∀φ∈fs,Complexity .sigma α φ) →
    Complexity .sigma α (sigmaList fs) ∧
      ∀ (G:Type) [AddCommGroup G] (a:Fin n→G),
        (sigmaList fs).Realize a ↔ ∀φ∈fs,φ.Realize a := by
  have hα : α≠0 := by
    intro hz
    subst α
    exact not_le_of_gt (show (0:Ordinal.{0})<2 from zero_lt_two) htwo
  induction fs with
  | nil =>
    intro _
    have hp := sigma_qf_padding.{0,0} α hα n (QF.equal .zero .zero)
    refine ⟨hp.1,?_⟩
    intro G _ a
    constructor
    · intro _ φ hφ
      simp only [List.not_mem_nil] at hφ
    · intro _
      exact (hp.2 G a).mpr rfl
  | cons φ fs ih =>
    intro hs
    obtain ⟨hf,hr⟩ := ih (fun ψ hψ=>hs ψ (List.mem_cons_of_mem φ hψ))
    refine ⟨higher_sigma_conjunction_complexity α htwo n φ (sigmaList fs)
      (hs φ (List.mem_cons_self)) hf,?_⟩
    intro G _ a
    change (sigmaTwoConjunction φ (sigmaList fs)).Realize a ↔ _
    rw [sigma_two_conjunction_realization G n φ (sigmaList fs) a,hr G a]
    simp only [List.forall_mem_cons]

private theorem countable_below {a b:Ordinal.{0}} (h:a≤b) (hb:Countable b.ToType) :
    Countable a.ToType := by
  letI := hb
  apply Cardinal.mk_le_aleph0_iff.mp
  rw [Cardinal.mk_toType]
  exact (Ordinal.card_le_card h).trans
    (by simpa only [Cardinal.mk_toType] using Cardinal.mk_le_aleph0 (α:=b.ToType))

private theorem height_or_tail (G:Type) [AddCommGroup G] (p:ℕ) (α:Ordinal.{0}) :
    ∀x:G, x∈(transfiniteFiltration p α:AddSubgroup G) ∨
      ∃β<α, x∈(transfiniteFiltration p β:AddSubgroup G) ∧
        x∉(transfiniteFiltration p (β+1):AddSubgroup G) := by
  classical
  refine Ordinal.limitRecOn α ?_ (fun β ih=>?_) (fun β hβ ih=>?_)
  · intro x
    exact Or.inl (by simp only [transfiniteFiltration_zero,AddSubgroup.mem_top])
  · intro x
    have hstep : β<β+1 := by simpa only [Order.succ_eq_add_one] using Order.lt_succ β
    by_cases hx:x∈(transfiniteFiltration p (β+1):AddSubgroup G)
    · exact Or.inl hx
    · rcases ih x with hprev|⟨ξ,hξ,hmem,hnot⟩
      · exact Or.inr ⟨β,hstep,hprev,hx⟩
      · exact Or.inr ⟨ξ,hξ.trans hstep,hmem,hnot⟩
  · intro x
    by_cases hx:x∈(transfiniteFiltration p β:AddSubgroup G)
    · exact Or.inl hx
    · have hn : ¬∀ξ:Set.Iio β, x∈(transfiniteFiltration p ξ.1:AddSubgroup G) := by
        intro hall
        apply hx
        rw [transfiniteFiltration_limit p hβ]
        exact AddSubgroup.mem_iInf.mpr hall
      obtain ⟨ξ,hξ⟩ := not_forall.mp hn
      rcases ih ξ.1 ξ.2 x with hmem|⟨η,hη,hmem,hnot⟩
      · exact (hξ hmem).elim
      · exact Or.inr ⟨η,hη.trans ξ.2,hmem,hnot⟩

private theorem finite_same_height (G:Type) [AddCommGroup G] (p:ℕ)
    (ξ:Ordinal.{0}) (x y:G)
    (hx:x∈(transfiniteFiltration p ξ:AddSubgroup G))
    (hx':x∉(transfiniteFiltration p (ξ+1):AddSubgroup G))
    (hy:y∈(transfiniteFiltration p ξ:AddSubgroup G))
    (hy':y∉(transfiniteFiltration p (ξ+1):AddSubgroup G)) :
    ∀β:Ordinal.{0}, y∈(transfiniteFiltration p β:AddSubgroup G) ↔
      x∈(transfiniteFiltration p β:AddSubgroup G) := by
  intro β
  by_cases hb:β≤ξ
  · exact ⟨fun _=>transfiniteFiltration_antitone p hb hx,
      fun _=>transfiniteFiltration_antitone p hb hy⟩
  · have hs : ξ+1≤β := by
      simpa only [Order.succ_eq_add_one] using Order.succ_le_of_lt (lt_of_not_ge hb)
    exact ⟨fun h=>(hy' (transfiniteFiltration_antitone p hs h)).elim,
      fun h=>(hx' (transfiniteFiltration_antitone p hs h)).elim⟩

private theorem normal_block_below (ξ η γ:Ordinal.{0}) (k:ℕ)
    (he:ξ=Ordinal.omega0*η+k) (hξ:ξ<Ordinal.omega0*γ) : η<γ := by
  by_contra h
  have hm : Ordinal.omega0*γ≤Ordinal.omega0*η :=
    mul_le_mul_left' (le_of_not_gt h) Ordinal.omega0
  exact not_le_of_gt hξ (hm.trans (by rw [he]; exact le_self_add))

private theorem odd_block_below (η γ:Ordinal.{0}) (h:η<γ) : 2*η+1<2*γ := by
  have hm : 2*η+2≤(2:Ordinal.{0})*γ := by
    simpa only [Order.succ_eq_add_one,mul_add_one] using
      mul_le_mul_left' (Order.succ_le_of_lt h) (2:Ordinal.{0})
  exact ((add_lt_add_iff_left (2*η)).mpr one_lt_two).trans_le hm

private theorem twice_positive_bound (γ:Ordinal.{0}) (hγ:0<γ) : 2≤2*γ := by
  have h := mul_le_mul_left' (Order.one_le_iff_ne_zero.mpr (ne_of_gt hγ)) (2:Ordinal.{0})
  simpa only [mul_one] using h

private theorem hom_term {G H:Type} [AddCommGroup G] [AddCommGroup H]
    (f:G→+H) (n:ℕ) (a:Fin n→G) (t:GroupTerm n) :
    f (t.eval a)=t.eval (fun i=>f (a i)) := by
  induction t with
  | var i => rfl
  | zero => exact f.map_zero
  | neg t ih => exact (f.map_neg _).trans (congrArg Neg.neg ih)
  | add s t ihs iht =>
    change f (s.eval a+t.eval a)=_
    rw [map_add,ihs,iht]
    rfl

private theorem automorphism_term (G:Type) [AddCommGroup G]
    (u:G≃+G) (n:ℕ) (a b:Fin n→G) (hu:∀i,u (a i)=b i) (t:GroupTerm n) :
    u (t.eval a)=t.eval b := by
  have h := hom_term u.toAddMonoidHom n a t
  change u (t.eval a)=t.eval (fun i=>u (a i)) at h
  rw [funext hu] at h
  exact h

private theorem generated_iso_term (G:Type) [AddCommGroup G] (n:ℕ) (a b:Fin n→G)
    (e:AddSubgroup.closure (Set.range a)≃+AddSubgroup.closure (Set.range b))
    (he:∀i,(e ⟨a i,AddSubgroup.subset_closure ⟨i,rfl⟩⟩:G)=b i) (t:GroupTerm n) :
    (e ⟨t.eval a,term_closure_membership G n a t⟩:G)=t.eval b := by
  let A := AddSubgroup.closure (Set.range a)
  let B := AddSubgroup.closure (Set.range b)
  let c : Fin n→A := fun i=>⟨a i,AddSubgroup.subset_closure ⟨i,rfl⟩⟩
  have hinput : t.eval c=⟨t.eval a,term_closure_membership G n a t⟩ :=
    Subtype.ext (hom_term A.subtype n c t)
  have houtput : (fun i=>(e (c i):G))=b := funext he
  have h := hom_term (B.subtype.comp e.toAddMonoidHom) n c t
  change (e (t.eval c):G)=t.eval (fun i=>(e (c i):G)) at h
  rwa [hinput,houtput] at h

private theorem equiv_height (G:Type) [AddCommGroup G] (p:ℕ) (u:G≃+G)
    (x:G) (α:Ordinal.{0}) : u x∈(transfiniteFiltration p α:AddSubgroup G) ↔
      x∈(transfiniteFiltration p α:AddSubgroup G) := by
  have hk : u.toAddMonoidHom.ker≤(transfiniteFiltration p α:AddSubgroup G) := by
    rw [u.toAddMonoidHom.ker_eq_bot u.injective]
    exact bot_le
  have hm := map_transfiniteFiltration_below p u.toAddMonoidHom u.surjective α hk α le_rfl
  constructor
  · intro hx
    have hmap : u x∈(transfiniteFiltration p α:AddSubgroup G).map u.toAddMonoidHom := by
      rw [hm]
      exact hx
    obtain ⟨y,hy,he⟩ := hmap
    exact (u.injective he) ▸ hy
  · intro hx
    rw [←hm]
    exact ⟨x,hx,rfl⟩


private theorem proper_cut_height_formula (p:ℕ) [Fact p.Prime] (G:Type)
    [AddCommGroup G] (γ:Ordinal.{0}) [Countable γ.ToType] (hγ:0<γ)
    (n:ℕ) (a:Fin n→G) (t:GroupTerm n)
    (hx:t.eval a∉(transfiniteFiltration p (Ordinal.omega0*γ):AddSubgroup G)) :
    ∃φ:Formula n, Complexity .sigma (2*γ+1) φ ∧ ∀b:Fin n→G,
      φ.Realize b ↔ ∀ξ:Ordinal.{0},t.eval b∈(transfiniteFiltration p ξ:AddSubgroup G) ↔
        t.eval a∈(transfiniteFiltration p ξ:AddSubgroup G) := by
  classical
  have htwo:=twice_positive_bound γ hγ
  have hlevel:(2*γ:Ordinal.{0})≠0 := by
    intro hz
    rw [hz] at htwo
    exact not_le_of_gt (show (0:Ordinal.{0})<2 from zero_lt_two) htwo
  rcases height_or_tail G p (Ordinal.omega0*γ) (t.eval a) with htail|⟨ξ,hξ,hmem,hnot⟩
  · exact (hx htail).elim
  · have hδcount:Countable (Ordinal.omega0*γ).ToType := by
      apply Cardinal.mk_le_aleph0_iff.mp
      rw [Cardinal.mk_toType,Ordinal.card_mul,Ordinal.card_omega0]
      have hcard:γ.card≤Cardinal.aleph0 := by
        simpa only [Cardinal.mk_toType] using Cardinal.mk_le_aleph0 (α:=γ.ToType)
      exact (mul_le_mul_left' hcard Cardinal.aleph0).trans_eq Cardinal.aleph0_mul_aleph0
    have hξcount:=countable_below hξ.le hδcount
    obtain ⟨z,hz,_⟩ := countable_length_normal_form ξ hξcount
    letI:Countable z.1.ToType:=hz.1
    have hb:=normal_block_below ξ z.1 γ z.2 hz.2 hξ
    have hbound:=odd_block_below z.1 γ hb
    obtain ⟨left,hl,hlsem⟩ := finite_offset_membership_definable p z.1 z.2 n t
    obtain ⟨next,hn,hnsem⟩ := finite_offset_membership_definable p z.1 (z.2+1) n t
    let neg:=sigmaWrap next.dual
    have hneg:Complexity .sigma (2*γ) neg := sigma_wrap_complexity (2*γ)
      (2*z.1+1) hlevel hbound n next.dual (dual_complexity .sigma (2*z.1+1) n next hn)
    have hleft:Complexity .sigma (2*γ) left :=
      GroupInfinitary.positive_complexity_monotone .sigma (2*z.1+1) (2*γ)
        n left (by simp) hbound.le hl
    let θ:=sigmaTwoConjunction left neg
    have hθ:Complexity .sigma (2*γ) θ := higher_sigma_conjunction_complexity (2*γ) htwo n left neg hleft hneg
    refine ⟨θ,GroupInfinitary.positive_complexity_monotone .sigma (2*γ) (2*γ+1)
      n θ hlevel le_self_add hθ,?_⟩
    intro b
    have hlb:left.Realize b ↔ t.eval b∈(transfiniteFiltration p ξ:AddSubgroup G) := by
      simpa only [←hz.2] using hlsem G b
    have he:Ordinal.omega0*z.1+((z.2+1:ℕ):Ordinal.{0})=ξ+1 := by
      rw [Nat.cast_add,Nat.cast_one,←add_assoc,←hz.2]
    have hnb:next.Realize b ↔ t.eval b∈(transfiniteFiltration p (ξ+1):AddSubgroup G) := by
      simpa only [he] using hnsem G b
    have hnegb:neg.Realize b ↔ t.eval b∉(transfiniteFiltration p (ξ+1):AddSubgroup G) :=
      ((sigma_wrap_realization G n next.dual b).trans (dual_realization G n next b)).trans (not_congr hnb)
    rw [sigma_two_conjunction_realization G n left neg b,hlb,hnegb]
    exact ⟨fun h=>finite_same_height G p ξ (t.eval a) (t.eval b) hmem hnot h.1 h.2,
      fun h=>⟨(h ξ).mpr hmem,fun hy=>hnot ((h (ξ+1)).mp hy)⟩⟩

private theorem tail_automorphism_height (G:Type) [AddCommGroup G] (p:ℕ) (δ:Ordinal.{0})
    (u:(transfiniteFiltration p δ:AddSubgroup G)≃+(transfiniteFiltration p δ:AddSubgroup G))
    (x:(transfiniteFiltration p δ:AddSubgroup G)) (α:Ordinal.{0}) :
    (u x:G)∈(transfiniteFiltration p α:AddSubgroup G) ↔ (x:G)∈(transfiniteFiltration p α:AddSubgroup G) := by
  by_cases hα:α≤δ
  · exact ⟨fun _=>transfiniteFiltration_antitone p hα x.property,
      fun _=>transfiniteFiltration_antitone p hα (u x).property⟩
  · have hδα:δ≤α:=le_of_not_ge hα
    rw [←Ordinal.add_sub_cancel_of_le hδα]
    rw [←transfinite_tail_membership G p δ (α-δ) (u x),
      ←transfinite_tail_membership G p δ (α-δ) x]
    exact equiv_height (transfiniteFiltration p δ:AddSubgroup G) p u x (α-δ)

theorem finite_socle_tail_tuple_orbits : Targets.finiteSocleTailTupleOrbits := by
  classical
  intro p _ G _ _ γ _ hγ hG hfin n a
  let δ:=Ordinal.omega0*γ
  let T:AddSubgroup G:=transfiniteFiltration p δ
  letI:Finite (pSocle p (⊤:AddSubgroup T)):=hfin
  have hT:∀x:T,∃k:ℕ,p^k • x=0 := by
    intro x
    obtain ⟨k,hk⟩ := hG (x:G)
    exact ⟨k,Subtype.ext hk⟩
  have htwo:2≤2*γ+1 := (twice_positive_bound γ hγ).trans le_self_add
  have hlevel:(2*γ+1:Ordinal.{0})≠0 := by simp
  let A:=AddSubgroup.closure (Set.range a)
  letI:Finite A:=p_primary_finite_tuple_closure G p (Fact.out:p.Prime).ne_zero hG n a
  letI:Fintype A:=Fintype.ofFinite A
  choose t ht using fun x:A=>closure_term_representation G n a (x:G) x.property
  let S:AddSubgroup T:=A.comap T.subtype
  let iS:S→A:=fun x=>⟨((x:T):G),x.property⟩
  have hiS:Function.Injective iS := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z:A=>(z:G)) h))
  letI:Finite S:=Finite.of_injective iS hiS
  letI:Fintype S:=Fintype.ofFinite S
  obtain ⟨K,hK,hSK,hwindow⟩ := finite_socle_embedding_window T p hT S
  letI:Finite K:=hK
  letI:Fintype K:=Fintype.ofFinite K
  let eS:=Fintype.equivFin S
  let s:Fin (Fintype.card S)→S:=eS.symm
  let aK:Fin (Fintype.card S)→K:=fun i=>⟨(s i:T),hSK (s i).property⟩
  let ts:Fin (Fintype.card S)→GroupTerm n:=fun i=>t (iS (s i))
  let table:=pointedTableFormula K n (Fintype.card S) aK ts
  have htable:Complexity .sigma (1:Ordinal.{0}) table :=
    (pointed_finite_table_correct K n (Fintype.card S) aK ts).1
  obtain ⟨τ,hτ,hτsem⟩ := low_transfinite_relativization p γ .sigma 1 (Or.inl rfl) n table (by simpa only [Nat.cast_one] using htable)
  have hτ':Complexity .sigma (2*γ+1) τ := by simpa only [Nat.cast_one] using hτ
  have hτextract:∀b:Fin n→G,τ.Realize b ↔
      ∃f:K→+T,Function.Injective f ∧ ∀i,(f (aK i):G)=(ts i).eval b := by
    intro b
    exact (hτsem G b).trans (pointed_finite_table_relative_correct K n (Fintype.card S) aK ts G T b)
  have hprofiles:∀x:A,∃φ:Formula n,Complexity .sigma (2*γ+1) φ ∧
      ∀b:Fin n→G,φ.Realize b ↔ ((x:G)∉T→∀ξ:Ordinal.{0},
        (t x).eval b∈(transfiniteFiltration p ξ:AddSubgroup G) ↔ (x:G)∈(transfiniteFiltration p ξ:AddSubgroup G)) := by
    intro x
    by_cases hx:(x:G)∈T
    · have hp:=sigma_qf_padding.{0,0} (2*γ+1) hlevel n (QF.equal .zero .zero)
      refine ⟨sigmaQF (.equal .zero .zero),hp.1,?_⟩
      intro b
      rw [hp.2 G b]
      constructor
      · intro _ hn
        exact (hn hx).elim
      · intro _
        rfl
    · have hx':(t x).eval a∉(transfiniteFiltration p (Ordinal.omega0*γ):AddSubgroup G) := by
        simpa only [ht x] using hx
      obtain ⟨φ,hφ,hsem⟩ := proper_cut_height_formula p G γ hγ n a (t x) hx'
      refine ⟨φ,hφ,?_⟩
      intro b
      rw [hsem b]
      simp only [ht x]
      exact ⟨fun h _=>h,fun h=>h hx⟩
  choose θ hθ hθsem using hprofiles
  obtain ⟨q,_,hqsem⟩ := p_primary_atomic_isolation p (Fact.out:p.Prime) G hG n a
  have hq:=sigma_qf_padding.{0,0} (2*γ+1) hlevel n q
  let xs:List A:=Finset.univ.toList
  let fs:List (Formula n):=τ::sigmaQF q::xs.map θ
  have hcomplex:∀φ∈fs,Complexity .sigma (2*γ+1) φ := by
    intro φ hφ
    rcases List.mem_cons.mp hφ with rfl|hφ
    · exact hτ'
    rcases List.mem_cons.mp hφ with rfl|hφ
    · exact hq.1
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hφ
    exact hθ x
  obtain ⟨hc,hsem⟩ := sigma_list_exact (2*γ+1) htwo n fs hcomplex
  refine ⟨sigmaList fs,hc,?_⟩
  intro b
  rw [hsem G b]
  constructor
  · intro hall
    have hqb:q.Realize b := (hq.2 G b).mp (hall _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
    obtain ⟨e,he⟩ := (atomic_generated_iso G G n a b).mp ((hqsem G b).mp hqb)
    obtain ⟨f,hf,ha⟩ := (hτextract b).mp (hall _ (List.mem_cons_self))
    obtain ⟨u,hu⟩ := hwindow f hf
    let F:FiniteHeightIso p G G :=
      { domain:=A
        codomain:=AddSubgroup.closure (Set.range b)
        finite_domain:=inferInstance
        equiv:=e
        preserves:=by
          intro x ξ
          have hrep:(⟨(t x).eval a,term_closure_membership G n a (t x)⟩:A)=x := Subtype.ext (ht x)
          have heval:=generated_iso_term G n a b e he (t x)
          rw [hrep] at heval
          rw [heval]
          by_cases hx:(x:G)∈T
          · let xS:S:=⟨⟨(x:G),hx⟩,x.property⟩
            have hObs:=ha (eS xS)
            have hux:(u ⟨(x:G),hx⟩:G)=(t x).eval b := by
              have huS:=congrArg (fun z:T=>(z:G)) (hu xS)
              exact huS.trans (by simpa only [aK,ts,s,iS,xS,eS,Equiv.symm_apply_apply] using hObs)
            rw [←hux]
            exact tail_automorphism_height G p δ u ⟨(x:G),hx⟩ ξ
          · have hθx:θ x∈fs := List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_map.mpr ⟨x,Finset.mem_toList.mpr (Finset.mem_univ x),rfl⟩))
            exact (hθsem x b).mp (hall (θ x) hθx) hx ξ }
    obtain ⟨v,hv⟩ := countable_primary_finite_height_homogeneity G p hG F
    refine ⟨v,?_⟩
    intro i
    exact (hv ⟨a i,AddSubgroup.subset_closure ⟨i,rfl⟩⟩).trans (he i)
  · rintro ⟨u,hu⟩ φ hφ
    rcases List.mem_cons.mp hφ with rfl|hφ
    · apply (hτextract b).mpr
      let v:T→+T := (u.toAddMonoidHom.comp T.subtype).codRestrict T (fun x=>
        (equiv_height G p u (x:G) δ).mpr x.property)
      let f:K→+T:=v.comp K.subtype
      refine ⟨f,?_,?_⟩
      · intro x y h
        apply Subtype.ext
        apply Subtype.ext
        exact u.injective (congrArg (fun z:T=>(z:G)) h)
      · intro i
        have h:=automorphism_term G u n a b hu (ts i)
        have hv:(ts i).eval a=((s i:T):G):=ht (iS (s i))
        rw [hv] at h
        exact h
    rcases List.mem_cons.mp hφ with rfl|hφ
    · apply (hq.2 G b).mpr
      apply (hqsem G b).mpr
      intro s t
      constructor
      · intro h
        exact ((automorphism_term G u n a b hu s).symm.trans
          ((congrArg u h).trans (automorphism_term G u n a b hu t)))
      · intro h
        exact u.injective ((automorphism_term G u n a b hu s).trans
          (h.trans (automorphism_term G u n a b hu t).symm))
    · obtain ⟨x,_,rfl⟩ := List.mem_map.mp hφ
      apply (hθsem x b).mpr
      intro _ ξ
      rw [←automorphism_term G u n a b hu (t x),←ht x]
      exact equiv_height G p u ((t x).eval a) ξ
end LogicLineages.ModelsAlgebra.PGroups
