import LogicLineages.PersistentMarking.MarkedConstructorOperatorTargets
import LogicLineages.PersistentMarking.MarkedConstructorCoherentProof
import LogicLineages.PersistentMarking.MarkedConstructorInputOrderProof
import LogicLineages.PersistentMarking.MarkedConstructorFamilyOrderProof

namespace LogicLineages.PersistentMarking.MarkedConstructorEncodingProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open MarkedFamilyParameters (Parameter)
open MarkedFamilyCoherence (InputLE weakenParameter)
open MarkedConstructorTargets (PrefixClosed)
open MarkedConstructorOperator

theorem encodeAt (S : Signature) (E : Environment) (heads : List Head) (M : Code) (p : Parameter)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E heads)
    (hp : MarkedFamilyParameters.Valid E heads p) :
    nextFamily S E heads M p ∈ (descriptor E p.2.1).carriers p.2.2.1 ∧
      ValueEq E p.2.1 p.2.2.1
        (HereditaryDomainSemantics.decode E p.2.1 p.2.2.1 (nextFamily S E heads M p))
        (MarkedConstructorValue.build S E heads M p) :=
  HereditaryEncodeDecodeProof.encodeDecode E p.2.1 p.2.2.1 _ hp.2.2.1
    (MarkedConstructorValidityProof.valid S E heads M p hc hm hp)

theorem nextInputOrder (S : Signature) (E : Environment) (heads : List Head) (M : Code)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E heads) :
    MarkedFamilyCoherence.Monotone E heads (nextFamily S E heads M) := by
  intro p q hp hq hpq
  rcases p with ⟨f,ρ,Γ,bs,es⟩
  rcases q with ⟨g,υ,Δ,cs,fs⟩
  have hρ := hpq.2.1
  have hΓ := hpq.2.2.1
  change ρ = υ at hρ
  change Γ = Δ at hΓ
  subst υ
  subst Δ
  have hP := encodeAt S E heads M (f,ρ,Γ,bs,es) hc hm hp
  have hQ := encodeAt S E heads M (g,ρ,Γ,cs,fs) hc hm hq
  have hsem := MarkedConstructorInputOrderProof.inputMonotone S E heads M _ _ hc hm hp hq hpq
  exact (HereditaryCodeOrderProof.exactOrder E ρ Γ _ _ hp.2.2.1 hP.1 hQ.1).mpr
    (HereditaryValueEqualityProof.order (HereditaryValueEqualityProof.symm hP.2)
      (HereditaryValueEqualityProof.symm hQ.2) hsem)

theorem nextCoherent (S : Signature) (E : Environment) (heads : List Head) (M : Code)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E heads) :
    MarkedFamilyCoherence.Coherent E heads (nextFamily S E heads M) := by
  intro p hp Δ hd he
  let q := weakenParameter E p Δ
  have hq := MarkedFamilyCoherenceFoundationProof.destinationValid E heads p Δ hp hd he
  have hP := encodeAt S E heads M p hc hm hp
  have hQ := encodeAt S E heads M q hc hm hq
  have hr := HereditaryRestrictionProof.restriction E p.2.1 p.2.2.1 Δ hp.2.2.1 hd he _ hP.1
  have hsem := MarkedConstructorCoherentProof.coherent S E heads M p Δ hc hm hp hd he
  exact HereditaryEncodingCongruenceProof.injective E p.2.1 Δ _ _ hr.1 hQ.1
    (HereditaryValueEqualityProof.trans hr.2
      (HereditaryValueEqualityProof.trans (HereditaryValueEqualityProof.weaken he hP.2)
        (HereditaryValueEqualityProof.trans hsem (HereditaryValueEqualityProof.symm hQ.2))))

end LogicLineages.PersistentMarking.MarkedConstructorEncodingProof
