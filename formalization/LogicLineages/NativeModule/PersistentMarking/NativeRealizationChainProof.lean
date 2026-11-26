module

public import LogicLineages.NativeModule.PersistentMarking.NativeRealizationChainTargets
import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalRealizationProof

public section

namespace LogicLineages.PersistentMarking.NativeRealizationChain
open Spine NativeCarrierTargets NativeIndexedCarrierTargets NativeIteratorStrictTargets
open NativeClosedApplication OrdinalRealizationTargets NativeOrdinalRealizationTargets

theorem exactChainOfStrict : ExactChainOfStrict := by
  intro terms wf strict A s t v chain realized
  induction chain with
  | single edge => exact strict A _ t v edge realized
  | tail _ edge ih => exact strict A _ _ v edge ih

theorem nativeRealizationFiniteChains : NativeRealizationFiniteChains := by
  intro S
  obtain ⟨wf,strict,_,_⟩ := NativeOrdinalRealizationProof.exact_NativeRealizationClosure.2.2 S
  exact ⟨wf,exactChainOfStrict (nativeTerms S) wf strict⟩

#print axioms exactChainOfStrict
#print axioms nativeRealizationFiniteChains
end LogicLineages.PersistentMarking.NativeRealizationChain
