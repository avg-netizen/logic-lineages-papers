import LogicLineages.PersistentMarking.MarkedFamilyCoherenceTargets
import LogicLineages.PersistentMarking.MarkedBaseTupleRestrictionProof
namespace LogicLineages.PersistentMarking.MarkedFamilyCoherenceFoundationProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics MarkedFamilyParameters MarkedFamilyCoding MarkedFamilyCoherence

theorem inputOrderExact : MarkedFamilyCoherenceTargets.InputOrderExact := by
  intro E heads p q hp hq
  rcases p with ⟨f,τ,Γ,bs,es⟩
  rcases q with ⟨g,υ,Δ,cs,fs⟩
  simp only [MarkedFamilyCoherence.inputLe,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨hfg,htu⟩,hgd⟩,hb⟩,he⟩
    subst g; subst υ; subst Δ
    exact ⟨rfl,rfl,rfl,(MarkedBaseTupleFoundationProof.orderExact E Γ f.arguments bs cs hp.2.2.2.1 hq.2.2.2.1).mp hb,
      he⟩
  · rintro ⟨hfg,htu,hgd,hb,he⟩
    change f=g at hfg
    change τ=υ at htu
    change Γ=Δ at hgd
    subst g; subst υ; subst Δ
    exact ⟨⟨⟨⟨rfl,rfl⟩,rfl⟩,(MarkedBaseTupleFoundationProof.orderExact E Γ f.arguments bs cs hp.2.2.2.1 hq.2.2.2.1).mpr hb⟩,
      he⟩

theorem destinationValid : MarkedFamilyCoherenceTargets.DestinationValid := by
  intro E heads p Δ hp hw he
  rcases p with ⟨f,τ,Γ,bs,es⟩
  exact ⟨hp.1,hp.2.1,hw,
    MarkedBaseTupleRestrictionProof.restriction E Γ Δ f.arguments bs hp.2.2.1 hw he hp.2.2.2.1,
    MarkedExtrasRestrictionProof.weakening E Γ Δ es hp.2.2.1 hw he hp.2.2.2.2⟩
end LogicLineages.PersistentMarking.MarkedFamilyCoherenceFoundationProof
