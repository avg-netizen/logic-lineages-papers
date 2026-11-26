module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineHeadParameterProof
public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorInputOrderProof
public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorCoherentProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineHeadValueProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineInterpreterCore
open MarkedFamilyParameters (Parameter)
open MarkedFamilyCoherence (weakenParameter)
open MarkedConstructorTargets (PrefixClosed)

def headValue (marked : Bool) (S : Signature) (E : Environment) (heads : List Head) (M : Code)
    (p : Parameter) : Value :=
  if marked then MarkedConstructorValue.build S E heads M p else ordinaryHead S E heads M p

theorem table (marked : Bool) (S : Signature) (E : Environment) (heads : List Head) (M : Code)
    (p : Parameter) : (headValue marked S E heads M p).application =
      (MarkedConstructorValue.build S E heads M p).application := by cases marked <;> rfl

theorem valid (marked : Bool) (S : Signature) (E : Environment) (heads : List Head) (M : Code)
    (p : Parameter) (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E heads)
    (hp : MarkedFamilyParameters.Valid E heads p) :
    Valid E p.2.1 p.2.2.1 (headValue marked S E heads M p) := by
  cases marked <;> exact MarkedConstructorValidityProof.valid S E heads M p hc hm hp

theorem natural (marked : Bool) (S : Signature) (E : Environment) (heads : List Head) (M : Code)
    (p : Parameter) (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E heads)
    (hp : MarkedFamilyParameters.Valid E heads p) (Δ : Context)
    (hd : WellFormed E.types E.ports Δ) (he : Extends p.2.2.1 Δ) :
    ValueEq E p.2.1 Δ (headValue marked S E heads M p)
      (headValue marked S E heads M (weakenParameter E p Δ)) := by
  have h := MarkedConstructorCoherentProof.coherent S E heads M p Δ hc hm hp hd he
  cases marked with
  | true => exact h
  | false =>
    intro Θ ht hf
    have hfields := h Θ ht hf
    refine ⟨hfields.1,?_,hfields.2.2⟩
    intro t ht'
    have hb := hfields.2.1 t ht'
    have hw := MarkedConstructorParameterProof.weakenComposition E heads p Δ Θ hp hd ht he hf
    exact ⟨by
      change (funTest S E (weakenParameter E p Θ) t || _) =
        (funTest S E (weakenParameter E (weakenParameter E p Δ) Θ) t || _)
      rw [hw,hb.1],hb.2⟩

theorem funMonotone (S : Signature) (E : Environment) (heads : List Head) (p q : Parameter)
    (hp : MarkedFamilyParameters.Valid E heads p) (hq : MarkedFamilyParameters.Valid E heads q)
    (hle : MarkedFamilyCoherence.InputLE E p q) (t : Expr)
    (h : funTest S E p t = true) : funTest S E q t = true := by
  rcases p with ⟨f,τ,Γ,bs,es⟩
  rcases q with ⟨g,υ,Δ,cs,fs⟩
  obtain ⟨hf,ht,hΓ,hbase,_⟩ := hle
  change f = g at hf
  change τ = υ at ht
  change Γ = Δ at hΓ
  subst g
  subst υ
  subst Δ
  cases t with
  | head g ts =>
    simp only [funTest,Bool.and_eq_true,decide_eq_true_eq] at h ⊢
    have hbaseOrder := MarkedConstructorStatOrderProof.baseOrder E Γ f.arguments bs cs
      hp.2.2.1 hp.2.2.2.1 hq.2.2.2.1 hbase
    have hm := (MarkedConstructorOccurrenceProof.matching E Γ _ (MarkedConstructorTests.terms ts)).mp h.2
    exact ⟨h.1,(MarkedConstructorOccurrenceProof.matching E Γ _ _).mpr
      (MarkedConstructorStatOrderProof.matchOrder hm hbaseOrder)⟩
  | free σ x => cases h
  | bound σ i => cases h
  | lam σ body => cases h
  | marked g σ bs es => cases h

theorem monotone (marked : Bool) (S : Signature) (E : Environment) (heads : List Head) (M : Code)
    (p q : Parameter) (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E heads)
    (hp : MarkedFamilyParameters.Valid E heads p) (hq : MarkedFamilyParameters.Valid E heads q)
    (hle : MarkedFamilyCoherence.InputLE E p q) :
    HereditaryOrderTargets.SemanticLE E p.2.1 p.2.2.1 (headValue marked S E heads M p) (headValue marked S E heads M q) := by
  have h := MarkedConstructorInputOrderProof.inputMonotone S E heads M p q hc hm hp hq hle
  cases marked with
  | true => exact h
  | false =>
    intro Δ hd he
    have hfields := h Δ hd he
    have hwp := MarkedFamilyCoherenceFoundationProof.destinationValid E heads p Δ hp hd he
    have hwq := MarkedFamilyCoherenceFoundationProof.destinationValid E heads q Δ hq hd (hle.2.2.1 ▸ he)
    have hle' := MarkedConstructorParameterProof.weakenMonotone E heads p q Δ hp hq hle hd he
    refine ⟨hfields.1,?_,hfields.2.2⟩
    intro t ht
    have hbits := hfields.2.1 t ht
    refine ⟨?_,hbits.2⟩
    change (_ || _) = true → (_ || _) = true
    rw [Bool.or_eq_true,Bool.or_eq_true]
    exact Or.imp (funMonotone S E heads _ _ hwp hwq hle' t) hbits.1

end LogicLineages.PersistentMarking.ProtectedSpineHeadValueProof
