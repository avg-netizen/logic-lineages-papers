import LogicLineages.PersistentMarking.MarkedConstructorInventoryProof
import LogicLineages.PersistentMarking.MarkedConstructorEndomapProof
import LogicLineages.PersistentMarking.MarkedConstructorStabilizationProof

namespace LogicLineages.PersistentMarking.MarkedConstructorOperatorChecks
open MarkedConstructorOperator

theorem exact_Operator : MarkedConstructorOperatorTargets.Operator := by
  intro S s t σ τ hs ht hos hot
  have hc := MarkedConstructorInventoryProof.prefixClosed s t σ τ hs.1 ht.1 hos hot
  have he := MarkedConstructorEndomapProof.endomap S (environment s t) _ hc
  have hm := MarkedConstructorEndomapProof.monotone S (environment s t) _ hc
  exact ⟨he,hm,MarkedConstructorStabilizationProof.stabilizes S (environment s t) _ he hm⟩

#print axioms exact_Operator
end LogicLineages.PersistentMarking.MarkedConstructorOperatorChecks
