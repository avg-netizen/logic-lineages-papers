module

public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorTargets
public import LogicLineages.NativeModule.PersistentMarking.HereditaryCodeOrderProof

@[expose] public section

namespace LogicLineages.PersistentMarking.MarkedConstructorBitOrderProof
open Spine DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

theorem bitObservation (strict : Bool) (E : Environment) (σ : Ty) (Γ : Context) (a : Code) (t : Expr)
    (ha : a ∈ (descriptor E σ).carriers Γ)
    (ht : (if strict then (decode E σ Γ a).strict Γ t else (decode E σ Γ a).weak Γ t) = true) :
    t ∈ DecisionObservations.observations E.names E.ports Γ E.target σ := by
  let k : Key := ⟨Γ, if strict then .strict t else .weak t⟩
  have hx : ∃ i, lookup (layout E σ (canonicalLower E σ) Γ) a k = some i := by
    cases h : lookup (layout E σ (canonicalLower E σ) Γ) a k with
    | some i => exact ⟨i,rfl⟩
    | none =>
      exfalso
      cases strict <;> simp [k] at h <;> simpa [decode,h] using ht
  obtain ⟨i,hi⟩ := hx
  obtain ⟨b,hb,_⟩ := HereditaryLookupProof.lookupBound _ a k i
    ((HereditaryConstructionProof.effective E σ Γ a).mp ha).1 hi
  obtain ⟨Δ,_,_,hΓ,hk⟩ := (FiniteSchemaExactProof.exactSchema σ (lowerCodes σ (canonicalLower E σ))
    E.types E.names E.ports E.target Γ k b).mp hb
  change Γ = Δ at hΓ
  subst Δ
  rcases hk with ⟨hk,_⟩ | ⟨q,hq,hk,_⟩ | ⟨q,hq,hk,_⟩ | ⟨ds,τ,hpre,xs,hxs,hk,_⟩
  · cases strict <;> cases hk
  · cases strict
    · cases hk
      exact hq
    · cases hk
  · cases strict
    · cases hk
    · cases hk
      exact hq
  · cases strict <;> cases hk

theorem decodeMonotone (strict : Bool) (E : Environment) (σ : Ty) (Γ : Context)
    (a b : Code) (t : Expr) (hw : WellFormed E.types E.ports Γ)
    (ha : a ∈ (descriptor E σ).carriers Γ) (hb : b ∈ (descriptor E σ).carriers Γ)
    (hle : (descriptor E σ).le Γ a b = true)
    (h : (if strict then (decode E σ Γ a).strict Γ t else (decode E σ Γ a).weak Γ t) = true) :
    (if strict then (decode E σ Γ b).strict Γ t else (decode E σ Γ b).weak Γ t) = true := by
  have ht := bitObservation strict E σ Γ a t ha h
  have hbits := ((HereditaryCodeOrderProof.exactOrder E σ Γ a b hw ha hb).mp hle
    Γ hw (DecisionPortsProof.extensionRefl Γ)).2.1 t ht
  cases strict
  · exact hbits.1 h
  · exact hbits.2 h

theorem taggedMonotone (strict : Bool) (E : Environment) (Γ : Context)
    (a b : MarkedExtras.Tagged) (t : Expr) (hw : WellFormed E.types E.ports Γ)
    (ha : a.2 ∈ (descriptor E a.1).carriers Γ)
    (hb : b.2 ∈ (descriptor E b.1).carriers Γ)
    (hle : MarkedExtras.le E Γ a b = true)
    (h : MarkedConstructorTests.bit strict E Γ a t = true) :
    MarkedConstructorTests.bit strict E Γ b t = true := by
  obtain ⟨σ,c⟩ := a
  obtain ⟨τ,d⟩ := b
  simp only [MarkedExtras.le, Bool.and_eq_true, decide_eq_true_eq] at hle
  obtain ⟨rfl,hle⟩ := hle
  simp only [MarkedConstructorTests.bit, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨h.1,decodeMonotone strict E σ Γ c d t hw ha hb hle h.2⟩

end LogicLineages.PersistentMarking.MarkedConstructorBitOrderProof
