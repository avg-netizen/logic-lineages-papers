module
public import LogicLineages.ModelsAlgebra.PGroups.CountableUlmTargets
public import LogicLineages.ModelsAlgebra.PGroups.FiniteFullFiltrationExtension
public import Mathlib.Data.ZMod.QuotientGroup
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
namespace FiniteHeightIso
variable {p : ℕ} {G H : Type} [AddCommGroup G] [AddCommGroup H]

private theorem graph_functional (f : FiniteHeightIso p G H) {x : G} {a b : H}
    (ha : (x,a) ∈ f.graph) (hb : (x,b) ∈ f.graph) : a = b := by
  obtain ⟨hx,ha⟩ := ha
  obtain ⟨hx',hb⟩ := hb
  exact ha.symm.trans hb

private theorem graph_injective (f : FiniteHeightIso p G H) {x y : G} {a : H}
    (hx : (x,a) ∈ f.graph) (hy : (y,a) ∈ f.graph) : x = y := by
  obtain ⟨hx,ex⟩ := hx
  obtain ⟨hy,ey⟩ := hy
  exact congrArg Subtype.val (f.equiv.injective (Subtype.ext (ex.trans ey.symm)))

private theorem graph_zero (f : FiniteHeightIso p G H) : (0,0) ∈ f.graph := by
  refine ⟨f.domain.zero_mem, ?_⟩
  exact congrArg Subtype.val f.equiv.map_zero

private theorem graph_add (f : FiniteHeightIso p G H) {x y : G} {a b : H}
    (hx : (x,a) ∈ f.graph) (hy : (y,b) ∈ f.graph) : (x+y,a+b) ∈ f.graph := by
  obtain ⟨hx,ex⟩ := hx
  obtain ⟨hy,ey⟩ := hy
  refine ⟨f.domain.add_mem hx hy, ?_⟩
  calc
    (f.equiv ⟨x+y,f.domain.add_mem hx hy⟩ : H) =
        (f.equiv ⟨x,hx⟩ : H) + (f.equiv ⟨y,hy⟩ : H) :=
      congrArg Subtype.val (f.equiv.map_add ⟨x,hx⟩ ⟨y,hy⟩)
    _ = a+b := by rw [ex,ey]

private noncomputable def symm (f : FiniteHeightIso p G H) : FiniteHeightIso p H G := by
  letI : Finite f.domain := f.finite_domain
  exact
    { domain := f.codomain
      codomain := f.domain
      finite_domain := Finite.of_equiv f.domain f.equiv.toEquiv
      equiv := f.equiv.symm
      preserves := fun x α => by
        simpa only [AddEquiv.apply_symm_apply] using (f.preserves (f.equiv.symm x) α).symm }

private theorem graph_symm (f : FiniteHeightIso p G H) (x : G) (y : H) :
    (y,x) ∈ f.symm.graph ↔ (x,y) ∈ f.graph := by
  change (∃ hy : y ∈ f.codomain, (f.equiv.symm ⟨y,hy⟩ : G) = x) ↔
    ∃ hx : x ∈ f.domain, (f.equiv ⟨x,hx⟩ : H) = y
  constructor
  · rintro ⟨hy,rfl⟩
    exact ⟨(f.equiv.symm ⟨y,hy⟩).property, by simp⟩
  · rintro ⟨hx,rfl⟩
    exact ⟨(f.equiv ⟨x,hx⟩).property, by simp⟩

private theorem extend_left [Fact p.Prime]
    (hG : ∀ x : G, ∃ n : ℕ, p^n • x = 0)
    (hH : ∀ x : H, ∃ n : ℕ, p^n • x = 0)
    (δ : Ordinal.{0}) (hδ : Order.IsSuccLimit δ)
    (hz : (transfiniteFiltration p δ : AddSubgroup G) = ⊥)
    (hRank : ∀ α < δ, Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) ≤
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H)))
    (f : FiniteHeightIso p G H) (x : G) :
    ∃ g : FiniteHeightIso p G H, x ∈ g.domain ∧ f ≤ g := by
  classical
  letI : Finite f.domain := f.finite_domain
  obtain ⟨n,hn⟩ := hG x
  have hxfin : IsOfFinAddOrder x := isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    ⟨p^n, pow_pos (Fact.out : p.Prime).pos n, hn⟩
  letI : Finite (AddSubgroup.zmultiples x) := hxfin.finite_zmultiples.to_subtype
  let D := f.domain ⊔ AddSubgroup.zmultiples x
  let a : f.domain × AddSubgroup.zmultiples x → D := fun y =>
    ⟨(y.1 : G) + y.2, AddSubgroup.add_mem_sup y.1.property y.2.property⟩
  have ha : Function.Surjective a := by
    intro y
    obtain ⟨b,c,hbc⟩ := AddSubgroup.mem_sup'.mp y.property
    exact ⟨(b,c), Subtype.ext hbc⟩
  letI : Finite D := Finite.of_surjective a ha
  have hBD : f.domain ≤ D := le_sup_left
  have hcut : D ⊓ transfiniteFiltration p δ ≤ f.domain := by
    rw [hz, inf_bot_eq]
    exact bot_le
  obtain ⟨F,hF,hFa,hFp⟩ := finite_full_filtration_extension G H p hG hH D f.domain f.codomain
    f.equiv δ hδ hBD hcut f.preserves hRank
  let g : FiniteHeightIso p G H :=
    { domain := D
      codomain := F.range
      finite_domain := inferInstance
      equiv := AddMonoidHom.ofInjective hF
      preserves := fun y α => by
        change F y ∈ transfiniteFiltration p α ↔ (y : G) ∈ transfiniteFiltration p α
        exact hFp y α }
  refine ⟨g, AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples x), ?_⟩
  rintro ⟨y,z⟩ ⟨hy,he⟩
  refine ⟨hBD hy, ?_⟩
  change F ⟨y,hBD hy⟩ = z
  exact (hFa ⟨y,hy⟩).trans he

private theorem extend_right [Fact p.Prime]
    (hG : ∀ x : G, ∃ n : ℕ, p^n • x = 0)
    (hH : ∀ x : H, ∃ n : ℕ, p^n • x = 0)
    (δ : Ordinal.{0}) (hδ : Order.IsSuccLimit δ)
    (hz : (transfiniteFiltration p δ : AddSubgroup H) = ⊥)
    (hRank : ∀ α < δ, Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H)) ≤
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)))
    (f : FiniteHeightIso p G H) (y : H) :
    ∃ g : FiniteHeightIso p G H, y ∈ g.codomain ∧ f ≤ g := by
  obtain ⟨g,hg,hle⟩ := extend_left hH hG δ hδ hz hRank f.symm y
  refine ⟨g.symm,hg,?_⟩
  rintro ⟨x,z⟩ h
  exact (graph_symm g z x).mpr (hle ((graph_symm f x z).mpr h))

private theorem total_of_cofinals [Countable G] [Countable H]
    (f₀ : FiniteHeightIso p G H)
    (L : G → Order.Cofinal (FiniteHeightIso p G H))
    (R : H → Order.Cofinal (FiniteHeightIso p G H))
    (hL : ∀ x f, f ∈ L x ↔ x ∈ f.domain)
    (hR : ∀ y f, f ∈ R y ↔ y ∈ f.codomain) :
    ∃ e : G ≃+ H, (∀ x : f₀.domain, e x = (f₀.equiv x : H)) ∧
      ∀ (x : G) (α : Ordinal.{0}), e x ∈ transfiniteFiltration p α ↔ x ∈ transfiniteFiltration p α := by
  classical
  letI := Encodable.ofCountable (G ⊕ H)
  let C : G ⊕ H → Order.Cofinal (FiniteHeightIso p G H) := Sum.elim L R
  let I := Order.idealOfCofinals f₀ C
  have hleft (x : G) : ∃ f : FiniteHeightIso p G H, f ∈ I ∧ x ∈ f.domain := by
    obtain ⟨f,hf,hi⟩ := Order.cofinal_meets_idealOfCofinals f₀ C (Sum.inl x)
    exact ⟨f,hi,(hL x f).mp hf⟩
  choose f hf hx using hleft
  let value (x : G) : H := ((f x).equiv ⟨x,hx x⟩ : H)
  have hv (x : G) : (x,value x) ∈ (f x).graph := ⟨hx x,rfl⟩
  have hzero : value 0 = 0 := graph_functional (f 0) (hv 0) (graph_zero (f 0))
  have hadd (x y : G) : value (x+y) = value x + value y := by
    obtain ⟨m,hm,hxm,hym⟩ := I.directed _ (hf x) _ (hf y)
    obtain ⟨n,_,hmn,hzn⟩ := I.directed _ hm _ (hf (x+y))
    exact graph_functional n (hzn (hv (x+y))) (graph_add n (hmn (hxm (hv x))) (hmn (hym (hv y))))
  let F : G →+ H := { toFun := value, map_zero' := hzero, map_add' := hadd }
  have hinj : Function.Injective F := by
    intro x y he
    obtain ⟨m,_,hxm,hym⟩ := I.directed _ (hf x) _ (hf y)
    apply graph_injective m (hxm (hv x))
    have hy := hym (hv y)
    change value x = value y at he
    rw [← he] at hy
    exact hy
  have hsurj : Function.Surjective F := by
    intro y
    obtain ⟨g,hg,hgi⟩ := Order.cofinal_meets_idealOfCofinals f₀ C (Sum.inr y)
    have hy := (hR y g).mp hg
    let x : G := (g.equiv.symm ⟨y,hy⟩ : G)
    have hxy : (x,y) ∈ g.graph := ⟨(g.equiv.symm ⟨y,hy⟩).property, by simp [x]⟩
    obtain ⟨m,_,hfm,hgm⟩ := I.directed _ (hf x) _ hgi
    exact ⟨x,graph_functional m (hfm (hv x)) (hgm hxy)⟩
  let e := AddEquiv.ofBijective F ⟨hinj,hsurj⟩
  refine ⟨e, ?_, ?_⟩
  · intro x
    obtain ⟨m,_,hfm,h₀m⟩ := I.directed _ (hf x) _ (Order.mem_idealOfCofinals f₀ C)
    exact graph_functional m (hfm (hv x)) (h₀m ⟨x.property,rfl⟩)
  · intro x α
    exact (f x).preserves ⟨x,hx x⟩ α
end FiniteHeightIso

theorem countable_ulm_extends_at_zero_cut : Targets.countableUlmExtendsAtZeroCut := by
  intro G H _ _ _ _ p _ hG hH δ hδ hzG hzH hRank f
  let L (x : G) : Order.Cofinal (FiniteHeightIso p G H) :=
    { carrier := {g | x ∈ g.domain}
      isCofinal := fun g => FiniteHeightIso.extend_left hG hH δ hδ hzG
        (fun α hα => (hRank α hα).le) g x }
  let R (y : H) : Order.Cofinal (FiniteHeightIso p G H) :=
    { carrier := {g | y ∈ g.codomain}
      isCofinal := fun g => FiniteHeightIso.extend_right hG hH δ hδ hzH
        (fun α hα => (hRank α hα).ge) g y }
  exact FiniteHeightIso.total_of_cofinals f L R (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)

theorem countable_ulm_at_zero_cut : Targets.countableUlmAtZeroCut := by
  intro G H _ _ _ _ p _ hG hH δ hδ hzG hzH hRank
  let e₀ : (⊥ : AddSubgroup G) ≃+ (⊥ : AddSubgroup H) := AddEquiv.ofUnique
  let f : FiniteHeightIso p G H :=
    { domain := ⊥
      codomain := ⊥
      finite_domain := inferInstance
      equiv := e₀
      preserves := fun x α => by
        have hx : (x : G) = 0 := x.property
        have hy : (e₀ x : H) = 0 := (e₀ x).property
        simp only [hx,hy,AddSubgroup.zero_mem] }
  obtain ⟨e,_,_⟩ := countable_ulm_extends_at_zero_cut G H p hG hH δ hδ hzG hzH hRank f
  exact ⟨e⟩
end LogicLineages.ModelsAlgebra.PGroups
