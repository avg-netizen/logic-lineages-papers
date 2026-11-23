module

public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorTupleProof
public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorParameterProof
public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorTagOrderProof

@[expose] public section

namespace LogicLineages.PersistentMarking.MarkedConstructorAppendProof
open Spine DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open MarkedFamilyParameters (Parameter)
open MarkedFamilyCoherence (InputLE weakenParameter)

/-- The old-family coordinate read by the actual full-tuple table. -/
def appendParameter (E : Environment) (p : Parameter) (τ : Ty)
    (ds : List Ty) (xs : List Code) : Parameter :=
  (p.1, τ, p.2.2.1, p.2.2.2.1,
    StructuralActions.insertExtras E p.2.2.1 p.2.2.2.2 (ds.zip xs))

theorem appendValid (E : Environment) (heads : List Head) (p : Parameter)
    (τ : Ty) (ds : List Ty) (xs : List Code)
    (hp : MarkedFamilyParameters.Valid E heads p) (ht : τ ∈ E.types)
    (hds : ∀ ρ, ρ ∈ ds → ρ ∈ E.types) (hx : TupleValues E p.2.2.1 ds xs) :
    MarkedFamilyParameters.Valid E heads (appendParameter E p τ ds xs) :=
  ⟨hp.1, ht, hp.2.2.1, hp.2.2.2.1,
    StructuralExtraInsertionProof.valid E p.2.2.1 _ _ hp.2.2.1 hp.2.2.2.2
      (MarkedConstructorTupleProof.tupleTags E p.2.2.1 ds xs hds hx)⟩

theorem appendMonotone (E : Environment) (heads : List Head) (p q : Parameter)
    (τ : Ty) (ds : List Ty) (xs ys : List Code)
    (hp : MarkedFamilyParameters.Valid E heads p) (hq : MarkedFamilyParameters.Valid E heads q)
    (hle : InputLE E p q) (hds : ∀ ρ, ρ ∈ ds → ρ ∈ E.types)
    (hx : TupleValues E p.2.2.1 ds xs) (hy : TupleValues E q.2.2.1 ds ys)
    (hxy : ValuesLE E p.2.2.1 ds xs ys) :
    InputLE E (appendParameter E p τ ds xs) (appendParameter E q τ ds ys) := by
  rcases p with ⟨f, υ, Γ, bs, es⟩
  rcases q with ⟨g, ω, Δ, cs, fs⟩
  rcases hle with ⟨hfg, _, hΓΔ, hbase, hextras⟩
  change f = g at hfg
  change Γ = Δ at hΓΔ
  subst g
  subst Δ
  refine ⟨rfl, rfl, rfl, hbase, ?_⟩
  exact MarkedConstructorTagOrderProof.insertMonotone E Γ es fs (ds.zip xs) (ds.zip ys)
    hp.2.2.1 hp.2.2.2.2 hq.2.2.2.2
    (MarkedConstructorTupleProof.tupleTags E Γ ds xs hds hx)
    (MarkedConstructorTupleProof.tupleTags E Γ ds ys hds hy)
    hextras (MarkedConstructorTagOrderProof.zipOrder E Γ ds xs ys hx.1 hy.1 hxy)

theorem appendNatural (E : Environment) (heads : List Head) (p : Parameter)
    (Θ : Context) (τ : Ty) (ds : List Ty) (xs : List Code)
    (hp : MarkedFamilyParameters.Valid E heads p)
    (hw : WellFormed E.types E.ports Θ) (he : Extends p.2.2.1 Θ)
    (hds : ∀ ρ, ρ ∈ ds → ρ ∈ E.types) (hx : TupleValues E p.2.2.1 ds xs) :
    weakenParameter E (appendParameter E p τ ds xs) Θ =
      appendParameter E (weakenParameter E p Θ) τ ds (restrictValues E p.2.2.1 Θ ds xs) := by
  rcases p with ⟨f, υ, Γ, bs, es⟩
  change (f, τ, Θ, MarkedBaseTuples.restrictTuple E Γ Θ f.arguments bs,
      MarkedExtras.weaken E Γ Θ (StructuralActions.insertExtras E Γ es (ds.zip xs))) =
    (f, τ, Θ, MarkedBaseTuples.restrictTuple E Γ Θ f.arguments bs,
      StructuralActions.insertExtras E Θ (MarkedExtras.weaken E Γ Θ es)
        (ds.zip (restrictValues E Γ Θ ds xs)))
  have hz : ds.zip (restrictValues E Γ Θ ds xs) =
      (ds.zip xs).map (MarkedExtras.restricted E Γ Θ) :=
    HereditaryTupleRestrictionProof.zipRestricted ds xs
      (fun a => (descriptor E a.1).restrict Γ Θ a.2) hx.1
  rw [hz, StructuralExtraInsertionProof.natural E Γ Θ es _
      hp.2.2.1 hw he hp.2.2.2.2 (MarkedConstructorTupleProof.tupleTags E Γ ds xs hds hx)]

end LogicLineages.PersistentMarking.MarkedConstructorAppendProof
