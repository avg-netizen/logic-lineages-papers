import LogicLineages.PersistentMarking.MarkedConstructorSourceOpeningProof

namespace LogicLineages.PersistentMarking.MarkedConstructorSourceLookupChecks
open Spine DecisionInventory DecisionPorts DecisionObservations MarkedConstructorOperator

theorem exact_SourceLookup : MarkedConstructorSourceLookupTargets.SourceLookupExact := by
  intro S s t σ τ hs ht hos hot
  dsimp only
  intro M p hm hp
  let E := environment s t
  let heads := (inventory s t).sourceHeads
  refine ⟨MarkedConstructorSourceTupleProof.selectSuccess S s t σ τ hs ht hos hot M p hm hp,?_,?_⟩
  · intro g ts hobs u hu
    have htypes := DecisionObservedTypesProof.observedTypes S s t σ τ p.2.2.1 p.2.1
      (.head g ts) hs ht hos hot hp.2.2.1 hobs
    have hin := MarkedConstructorSourceTupleProof.argumentSupport ts u hu
    have htype : u.type ∈ auxiliarySupport (.head g ts) := List.mem_append_right _ hin
    exact MarkedConstructorSourceTupleProof.ownerSuccess E heads M p hm hp u.type (htypes u.type htype)
  · exact MarkedConstructorSourceOpeningProof.openingSuccess S s t σ τ hs ht hos hot M p hm hp

#print axioms exact_SourceLookup
end LogicLineages.PersistentMarking.MarkedConstructorSourceLookupChecks
