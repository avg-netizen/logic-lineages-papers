import LogicLineages.PersistentMarking.MarkedFamilyCoherenceFoundationProof
import LogicLineages.PersistentMarking.MarkedExtrasWeakeningProof

namespace LogicLineages.PersistentMarking.MarkedConstructorParameterProof
open Spine DecisionPorts HereditaryDomainCode HereditaryDomainSemantics
open MarkedFamilyParameters (Parameter)
open MarkedFamilyCoherence (InputLE weakenParameter)

theorem weakenComposition (E : Environment) (heads : List Head) (p : Parameter) (Δ Θ : Context)
    (hp : MarkedFamilyParameters.Valid E heads p)
    (hd : WellFormed E.types E.ports Δ) (ht : WellFormed E.types E.ports Θ)
    (he : Extends p.2.2.1 Δ) (hf : Extends Δ Θ) :
    weakenParameter E (weakenParameter E p Δ) Θ = weakenParameter E p Θ := by
  rcases p with ⟨f, τ, Γ, bs, es⟩
  change (f, τ, Θ, MarkedBaseTuples.restrictTuple E Δ Θ f.arguments
      (MarkedBaseTuples.restrictTuple E Γ Δ f.arguments bs),
      MarkedExtras.weaken E Δ Θ (MarkedExtras.weaken E Γ Δ es)) =
    (f, τ, Θ, MarkedBaseTuples.restrictTuple E Γ Θ f.arguments bs,
      MarkedExtras.weaken E Γ Θ es)
  rw [MarkedBaseTupleRestrictionProof.composition E Γ Δ Θ f.arguments bs
    hp.2.2.1 hd ht he hf hp.2.2.2.1,
    (MarkedExtrasWeakeningProof.algebra E).2 Γ Δ Θ es hp.2.2.1 hd ht he hf hp.2.2.2.2]

theorem weakenIdentity (E : Environment) (heads : List Head) (p : Parameter)
    (hp : MarkedFamilyParameters.Valid E heads p) : weakenParameter E p p.2.2.1 = p := by
  rcases p with ⟨f, τ, Γ, bs, es⟩
  change (f, τ, Γ, MarkedBaseTuples.restrictTuple E Γ Γ f.arguments bs,
    MarkedExtras.weaken E Γ Γ es) = (f, τ, Γ, bs, es)
  rw [MarkedBaseTupleRestrictionProof.identity E Γ f.arguments bs hp.2.2.1 hp.2.2.2.1,
    (MarkedExtrasWeakeningProof.algebra E).1 Γ es hp.2.2.1 hp.2.2.2.2]

theorem weakenMonotone (E : Environment) (heads : List Head) (p q : Parameter) (Δ : Context)
    (hp : MarkedFamilyParameters.Valid E heads p) (hq : MarkedFamilyParameters.Valid E heads q)
    (hle : InputLE E p q) (hd : WellFormed E.types E.ports Δ) (he : Extends p.2.2.1 Δ) :
    InputLE E (weakenParameter E p Δ) (weakenParameter E q Δ) := by
  rcases p with ⟨f, τ, Γ, bs, es⟩
  rcases q with ⟨g, υ, Θ, cs, fs⟩
  rcases hle with ⟨hfg, hτυ, hΓΘ, hbase, hextras⟩
  change f = g at hfg
  change τ = υ at hτυ
  change Γ = Θ at hΓΘ
  subst g
  subst υ
  subst Θ
  have hb := (MarkedBaseTupleFoundationProof.orderExact E Γ f.arguments bs cs
    hp.2.2.2.1 hq.2.2.2.1).mpr hbase
  have hbs := MarkedBaseTupleRestrictionProof.restriction E Γ Δ f.arguments bs
    hp.2.2.1 hd he hp.2.2.2.1
  have hcs := MarkedBaseTupleRestrictionProof.restriction E Γ Δ f.arguments cs
    hp.2.2.1 hd he hq.2.2.2.1
  refine ⟨rfl, rfl, rfl, (MarkedBaseTupleFoundationProof.orderExact E Δ f.arguments _ _ hbs hcs).mp
    (MarkedBaseTupleRestrictionProof.monotone E Γ Δ f.arguments bs cs hp.2.2.1 hd he
      hp.2.2.2.1 hq.2.2.2.1 hb), ?_⟩
  intro a ha
  obtain ⟨hm, source, hs, hle⟩ := (MarkedExtrasWeakeningProof.weakeningMember E Γ Δ es a).mp ha
  exact (MarkedExtrasWeakeningProof.weakeningMember E Γ Δ fs a).mpr ⟨hm, source, hextras source hs, hle⟩

end LogicLineages.PersistentMarking.MarkedConstructorParameterProof
