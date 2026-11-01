module
public import LogicLineages.ModelsAlgebra.PGroups.TupleOrbitTargets
public import LogicLineages.ModelsAlgebra.PGroups.CountableHomogeneityProof
public import LogicLineages.ModelsAlgebra.PGroups.HigherSigmaConjunctionProof
public import LogicLineages.ModelsAlgebra.PGroups.StableStageProof
public import LogicLineages.ModelsAlgebra.PGroups.ReducedLengthProof
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteMembershipProof
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryDual
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryWrap
public import LogicLineages.ModelsAlgebra.PGroups.FiniteAtomicIsolation
public import LogicLineages.ModelsAlgebra.PGroups.AtomicGeneratedIsoProof
public import LogicLineages.ModelsAlgebra.PGroups.PPrimaryFiniteGenerationProof
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

private theorem tail_same_height (G:Type) [AddCommGroup G] (p:ℕ) [Fact p.Prime]
    (hG:∀x:G,∃k:ℕ,p^k • x=0) (α:Ordinal.{0}) (hstable:StableAt p G α)
    (x y:G) (hx:x∈(transfiniteFiltration p α:AddSubgroup G))
    (hy:y∈(transfiniteFiltration p α:AddSubgroup G)) :
    ∀β:Ordinal.{0}, y∈(transfiniteFiltration p β:AddSubgroup G) ↔
      x∈(transfiniteFiltration p β:AddSubgroup G) := by
  have hs := primary_stable_stage G p hG α hstable
  intro β
  rcases lt_or_ge β α with hb|hb
  · exact ⟨fun _=>transfiniteFiltration_antitone p hb.le hx,
      fun _=>transfiniteFiltration_antitone p hb.le hy⟩
  · have he : (transfiniteFiltration p β:AddSubgroup G)=transfiniteFiltration p α :=
      (hs.2.2 β hb).1.trans hs.2.1.symm
    rw [he]
    exact ⟨fun _=>hx,fun _=>hy⟩

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

private theorem short_height_formula (p:ℕ) [Fact p.Prime] (G:Type)
    [AddCommGroup G] [Countable G] (γ:Ordinal.{0}) [Countable γ.ToType]
    (α:Ordinal.{0}) (hγ:0<γ) (hα:Countable α.ToType)
    (hG:∀x:G,∃k:ℕ,p^k • x=0) (hαγ:α<Ordinal.omega0*γ) (hstable:StableAt p G α)
    (n:ℕ) (a:Fin n→G) (t:GroupTerm n) :
    ∃φ:Formula n, Complexity .sigma (2*γ) φ ∧ ∀b:Fin n→G,
      φ.Realize b ↔ ∀ξ:Ordinal.{0}, t.eval b∈(transfiniteFiltration p ξ:AddSubgroup G) ↔
        t.eval a∈(transfiniteFiltration p ξ:AddSubgroup G) := by
  classical
  have htwo := twice_positive_bound γ hγ
  have hlevel : (2*γ:Ordinal.{0})≠0 := by
    intro hz
    rw [hz] at htwo
    exact not_le_of_gt (show (0:Ordinal.{0})<2 from zero_lt_two) htwo
  rcases height_or_tail G p α (t.eval a) with htail|⟨ξ,hξ,hmem,hnot⟩
  · obtain ⟨z,hz,_⟩ := countable_length_normal_form α hα
    letI : Countable z.1.ToType := hz.1
    have hb := normal_block_below α z.1 γ z.2 hz.2 hαγ
    have hbound := odd_block_below z.1 γ hb
    obtain ⟨φ,hφ,hsem⟩ := finite_offset_membership_definable p z.1 z.2 n t
    refine ⟨φ,GroupInfinitary.positive_complexity_monotone .sigma (2*z.1+1) (2*γ)
      n φ (by simp) hbound.le hφ,?_⟩
    intro b
    have hs : φ.Realize b ↔ t.eval b∈(transfiniteFiltration p α:AddSubgroup G) := by
      simpa only [←hz.2] using hsem G b
    rw [hs]
    exact ⟨fun hy=>tail_same_height G p hG α hstable (t.eval a) (t.eval b) htail hy,
      fun h=>(h α).mpr htail⟩
  · have hξcount := countable_below hξ.le hα
    obtain ⟨z,hz,_⟩ := countable_length_normal_form ξ hξcount
    letI : Countable z.1.ToType := hz.1
    have hb := normal_block_below ξ z.1 γ z.2 hz.2 (hξ.trans hαγ)
    have hbound := odd_block_below z.1 γ hb
    obtain ⟨left,hl,hlsem⟩ := finite_offset_membership_definable p z.1 z.2 n t
    obtain ⟨next,hn,hnsem⟩ := finite_offset_membership_definable p z.1 (z.2+1) n t
    let neg := sigmaWrap next.dual
    have hneg : Complexity .sigma (2*γ) neg := sigma_wrap_complexity (2*γ)
      (2*z.1+1) hlevel hbound n next.dual
      (dual_complexity .sigma (2*z.1+1) n next hn)
    have hleft : Complexity .sigma (2*γ) left :=
      GroupInfinitary.positive_complexity_monotone .sigma (2*z.1+1) (2*γ)
        n left (by simp) hbound.le hl
    refine ⟨sigmaTwoConjunction left neg,
      higher_sigma_conjunction_complexity (2*γ) htwo n left neg hleft hneg,?_⟩
    intro b
    have hlb : left.Realize b ↔ t.eval b∈(transfiniteFiltration p ξ:AddSubgroup G) := by
      simpa only [←hz.2] using hlsem G b
    have he : Ordinal.omega0*z.1+((z.2+1:ℕ):Ordinal.{0})=ξ+1 := by
      rw [Nat.cast_add,Nat.cast_one,←add_assoc,←hz.2]
    have hnb : next.Realize b ↔ t.eval b∈(transfiniteFiltration p (ξ+1):AddSubgroup G) := by
      simpa only [he] using hnsem G b
    have hnegb : neg.Realize b ↔ t.eval b∉(transfiniteFiltration p (ξ+1):AddSubgroup G) :=
      ((sigma_wrap_realization G n next.dual b).trans
        (dual_realization G n next b)).trans (not_congr hnb)
    rw [sigma_two_conjunction_realization G n left neg b,hlb,hnegb]
    exact ⟨fun h=>finite_same_height G p ξ (t.eval a) (t.eval b) hmem hnot h.1 h.2,
      fun h=>⟨(h ξ).mpr hmem,fun hy=>hnot ((h (ξ+1)).mp hy)⟩⟩

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

theorem short_stable_tuple_orbit_definable : Targets.shortStableTupleOrbitDefinable := by
  classical
  intro p _ G _ _ γ _ α hγ hα hG hαγ hstable n a
  have htwo := twice_positive_bound γ hγ
  have hlevel : (2*γ:Ordinal.{0})≠0 := by
    intro hz
    rw [hz] at htwo
    exact not_le_of_gt (show (0:Ordinal.{0})<2 from zero_lt_two) htwo
  let A := AddSubgroup.closure (Set.range a)
  letI : Finite A := p_primary_finite_tuple_closure G p (Fact.out:p.Prime).ne_zero hG n a
  letI : Fintype A := Fintype.ofFinite A
  choose t ht using fun x:A=>closure_term_representation G n a (x:G) x.property
  choose θ hθ hθsem using fun x:A=>
    short_height_formula p G γ α hγ hα hG hαγ hstable n a (t x)
  obtain ⟨q,_,hqsem⟩ := p_primary_atomic_isolation p (Fact.out:p.Prime) G hG n a
  have hq := sigma_qf_padding.{0,0} (2*γ) hlevel n q
  let xs : List A := Finset.univ.toList
  let fs : List (Formula n) := sigmaQF q::xs.map θ
  have hcomplex : ∀φ∈fs,Complexity .sigma (2*γ) φ := by
    intro φ hφ
    rcases List.mem_cons.mp hφ with rfl|hφ
    · exact hq.1
    · obtain ⟨x,_,rfl⟩ := List.mem_map.mp hφ
      exact hθ x
  obtain ⟨hc,hsem⟩ := sigma_list_exact (2*γ) htwo n fs hcomplex
  refine ⟨sigmaList fs,hc,?_⟩
  intro b
  rw [hsem G b]
  constructor
  · intro hall
    have hqb : q.Realize b := (hq.2 G b).mp (hall _ (List.mem_cons_self))
    obtain ⟨e,he⟩ := (atomic_generated_iso G G n a b).mp ((hqsem G b).mp hqb)
    let B := AddSubgroup.closure (Set.range b)
    let F : FiniteHeightIso p G G :=
      { domain:=A
        codomain:=B
        finite_domain:=inferInstance
        equiv:=e
        preserves:=by
          intro x ξ
          have hx : θ x∈fs := List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨x,Finset.mem_toList.mpr (Finset.mem_univ x),rfl⟩)
          have hh := (hθsem x b).mp (hall (θ x) hx) ξ
          have hrep : (⟨(t x).eval a,term_closure_membership G n a (t x)⟩:A)=x :=
            Subtype.ext (ht x)
          have heval := generated_iso_term G n a b e he (t x)
          rw [hrep] at heval
          rw [heval,←ht x]
          exact hh }
    obtain ⟨u,hu⟩ := countable_primary_finite_height_homogeneity G p hG F
    refine ⟨u,?_⟩
    intro i
    exact (hu ⟨a i,AddSubgroup.subset_closure ⟨i,rfl⟩⟩).trans (he i)
  · rintro ⟨u,hu⟩ φ hφ
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
      intro ξ
      rw [←automorphism_term G u n a b hu (t x)]
      exact equiv_height G p u ((t x).eval a) ξ

end LogicLineages.ModelsAlgebra.PGroups
