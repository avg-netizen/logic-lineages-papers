module

public import LogicLineages.NativeModule.PersistentMarking.MarkedExtrasDownProof

@[expose] public section

namespace LogicLineages.PersistentMarking.MarkedConstructorTagOrderProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

theorem zipOrder (E : Environment) (Γ : Context) (ds : List Ty) (xs ys : List Code)
    (hx : ds.length = xs.length) (hy : ds.length = ys.length) (hxy : ValuesLE E Γ ds xs ys) :
    ∀ a, a ∈ ds.zip xs → ∃ b, b ∈ ds.zip ys ∧ MarkedExtras.le E Γ a b = true := by
  induction ds generalizing xs ys with
  | nil => simp
  | cons σ ds ih =>
    cases xs with
    | nil => cases hx
    | cons x xs =>
      cases ys with
      | nil => cases hy
      | cons y ys =>
        intro a ha
        simp only [List.zip_cons_cons, List.mem_cons] at ha ⊢
        rcases ha with rfl | ha
        · exact ⟨(σ,y), Or.inl rfl, by
            simpa only [MarkedExtras.le, decide_true, Bool.true_and] using hxy 0 σ x y rfl rfl rfl⟩
        · have htail : ValuesLE E Γ ds xs ys := fun i τ u v hd hu hv =>
            hxy (i+1) τ u v hd hu hv
          obtain ⟨b,hb,hab⟩ := ih xs ys (Nat.succ.inj hx) (Nat.succ.inj hy) htail a ha
          exact ⟨b, Or.inr hb, hab⟩

theorem downMonotone (E : Environment) (Γ : Context) (xs ys : List MarkedExtras.Tagged)
    (hw : WellFormed E.types E.ports Γ)
    (hx : ∀ a, a ∈ xs → a ∈ MarkedExtras.«universe» E Γ)
    (hy : ∀ b, b ∈ ys → b ∈ MarkedExtras.«universe» E Γ)
    (hxy : ∀ a, a ∈ xs → ∃ b, b ∈ ys ∧ MarkedExtras.le E Γ a b = true) :
    ∀ a, a ∈ MarkedExtras.down E Γ xs → a ∈ MarkedExtras.down E Γ ys := by
  intro a ha
  obtain ⟨hm,x,hx',hax⟩ := (MarkedExtrasFoundationProof.downExact E Γ xs a).mp ha
  obtain ⟨y,hy',hxy'⟩ := hxy x hx'
  exact (MarkedExtrasFoundationProof.downExact E Γ ys a).mpr
    ⟨hm,y,hy',(MarkedExtrasFoundationProof.order E Γ hw).2.1 a x y hm (hx x hx') (hy y hy') hax hxy'⟩

theorem insertMonotone (E : Environment) (Γ : Context) (es fs xs ys : List MarkedExtras.Tagged)
    (hw : WellFormed E.types E.ports Γ)
    (he : MarkedExtras.Extra E Γ es) (hf : MarkedExtras.Extra E Γ fs)
    (hx : ∀ a, a ∈ xs → a ∈ MarkedExtras.«universe» E Γ)
    (hy : ∀ a, a ∈ ys → a ∈ MarkedExtras.«universe» E Γ)
    (hef : ∀ a, a ∈ es → a ∈ fs)
    (hxy : ∀ a, a ∈ xs → ∃ b, b ∈ ys ∧ MarkedExtras.le E Γ a b = true) :
    ∀ a, a ∈ MarkedExtras.down E Γ (es ++ xs) → a ∈ MarkedExtras.down E Γ (fs ++ ys) := by
  apply downMonotone E Γ _ _ hw
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact MarkedExtrasDownProof.canonicalMember E Γ es he.1 a ha
    · exact hx a ha
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact MarkedExtrasDownProof.canonicalMember E Γ fs hf.1 a ha
    · exact hy a ha
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact ⟨a, List.mem_append_left _ (hef a ha), (MarkedExtrasFoundationProof.order E Γ hw).1 a
        (MarkedExtrasDownProof.canonicalMember E Γ es he.1 a ha)⟩
    · obtain ⟨b,hb,hab⟩ := hxy a ha
      exact ⟨b, List.mem_append_right _ hb, hab⟩

end LogicLineages.PersistentMarking.MarkedConstructorTagOrderProof
