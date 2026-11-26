import LogicLineages.PersistentMarking.MarkedConstructorOwnerOrderProof
import LogicLineages.PersistentMarking.StructuralFullActionProof
import LogicLineages.PersistentMarking.MarkedConstructorTagOrderProof

namespace LogicLineages.PersistentMarking.MarkedConstructorSelectOrderProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open MarkedFamilyParameters (Parameter)
open MarkedFamilyCoherence (InputLE)
open MarkedConstructorOwnerOrderProof (OwnerOrder)

def selectedTags (p : Parameter) : List MarkedExtras.Tagged :=
  p.1.arguments.zip p.2.2.2.1 ++ p.2.2.2.2

theorem tagCarrier (E : Environment) (heads : List Head) (p : Parameter) (a : MarkedExtras.Tagged)
    (hp : MarkedFamilyParameters.Valid E heads p) (ha : a ∈ selectedTags p) :
    a.2 ∈ (descriptor E a.1).carriers p.2.2.1 := by
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp ha
    have ⟨hρ,hv⟩ := List.getElem?_zip_eq_some.mp hi
    exact hp.2.2.2.1.2 i a.1 a.2 hρ hv
  · have hm := MarkedExtrasDownProof.canonicalMember E p.2.2.1 p.2.2.2.2 hp.2.2.2.2.1 a ha
    exact ((MarkedExtrasFoundationProof.universeExact E p.2.2.1 a.1 a.2).mp hm).2

theorem tagsInputOrder (E : Environment) (heads : List Head) (p q : Parameter)
    (hp : MarkedFamilyParameters.Valid E heads p) (hq : MarkedFamilyParameters.Valid E heads q)
    (hpq : InputLE E p q) :
    ∀ a, a ∈ selectedTags p → ∃ b, b ∈ selectedTags q ∧ MarkedExtras.le E p.2.2.1 a b = true := by
  rcases p with ⟨f, τ, Γ, bs, es⟩
  rcases q with ⟨g, υ, Δ, cs, fs⟩
  rcases hpq with ⟨hfg,_,_,hb,he⟩
  change f = g at hfg
  subst g
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨b,hb,hle⟩ := MarkedConstructorTagOrderProof.zipOrder E Γ f.arguments bs cs
      hp.2.2.2.1.1 hq.2.2.2.1.1 hb a ha
    exact ⟨b,List.mem_append_left _ hb,hle⟩
  · have hu := MarkedExtrasDownProof.canonicalMember E Γ es hp.2.2.2.2.1 a ha
    exact ⟨a,List.mem_append_right _ (he a ha),(MarkedExtrasFoundationProof.order E Γ hp.2.2.1).1 a hu⟩

theorem selectOrder (E : Environment) (heads : List Head) (M N : Code) (p q : Parameter)
    (hp : MarkedFamilyParameters.Valid E heads p) (hq : MarkedFamilyParameters.Valid E heads q)
    (hτ : p.2.1 = q.2.1) (hΓ : p.2.2.1 = q.2.2.1) (t : Expr)
    (howner : OwnerOrder E heads M N p q)
    (htag : ∀ a, a ∈ selectedTags p → ∃ b, b ∈ selectedTags q ∧ MarkedExtras.le E p.2.2.1 a b = true)
    (h : MarkedConstructorTargets.SelectWitness E heads M p t) :
    MarkedConstructorTargets.SelectWitness E heads N q t := by
  rcases p with ⟨f,τ,Γ,bs,es⟩
  rcases q with ⟨g,υ,Δ,cs,fs⟩
  change τ = υ at hτ
  change Γ = Δ at hΓ
  subst υ
  subst Δ
  obtain ⟨a,ha,hselect⟩ := h
  obtain ⟨b,hb,hab⟩ := htag a ha
  have hac := tagCarrier E heads (f,τ,Γ,bs,es) a hp ha
  have hbc := tagCarrier E heads (g,τ,Γ,cs,fs) b hq hb
  have hab' := hab
  simp only [MarkedExtras.le, Bool.and_eq_true, decide_eq_true_eq] at hab'
  have hty := hab'.1
  refine ⟨b,hb,?_⟩
  rcases hselect with ⟨hτ,hbit⟩ | ⟨ds,xs,hpre,hxs,hbit⟩
  · exact Or.inl ⟨hty.symm.trans hτ, MarkedConstructorBitOrderProof.taggedMonotone
      false E Γ a b t hp.2.2.1 hac hbc hab hbit⟩
  · obtain ⟨ys,hys,hx,hy,hxy⟩ := MarkedConstructorOwnerOrderProof.tupleOrder E heads M N (f,τ,Γ,bs,es) (g,τ,Γ,cs,fs) howner ds xs hxs
    rcases a with ⟨α,a⟩
    rcases b with ⟨β,b⟩
    change α = β at hty
    subst β
    have hle : (descriptor E α).le Γ a b = true := hab'.2
    have hnew := StructuralFullActionProof.monotone E α Γ a b ds τ xs ys hp.2.2.1
      hac hbc hle hpre hx hy hxy
    have hleft := StructuralFullActionProof.sound E α Γ a ds τ xs hp.2.2.1 hac hpre hx
    have hright := StructuralFullActionProof.sound E α Γ b ds τ ys hp.2.2.1 hbc hpre hy
    exact Or.inr ⟨ds,ys,hpre,hys,
      MarkedConstructorBitOrderProof.decodeMonotone false E τ Γ _ _ t hp.2.2.1 hleft hright hnew hbit⟩

end LogicLineages.PersistentMarking.MarkedConstructorSelectOrderProof
