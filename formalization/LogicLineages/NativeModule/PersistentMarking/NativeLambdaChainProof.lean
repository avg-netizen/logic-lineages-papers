module

public import LogicLineages.NativeModule.PersistentMarking.NativeLambdaChainTargets
import LogicLineages.NativeModule.PersistentMarking.NativeRealizationChainProof
import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalRealizationProof

public section

namespace LogicLineages.PersistentMarking.NativeLambdaChain
open Spine NativeCarrierTargets NativeIndexedCarrierTargets NativeIteratorStrictTargets
open NativeClosedApplication OrdinalRealizationTargets NativeOrdinalRealizationTargets

theorem nativeLambdaChainRealization : NativeLambdaChainRealization := by
  intro S
  obtain ⟨wf,lambdaRule⟩ := NativeOrdinalRealizationProof.exact_NativeLambdaRealization S
  obtain ⟨_,strict,_,_⟩ := NativeOrdinalRealizationProof.exact_NativeRealizationClosure.2.2 S
  have chain := NativeRealizationChain.exactChainOfStrict (nativeTerms S) wf strict
  refine ⟨wf,?_⟩
  intro A D body hl f s bodies path
  exact chain (.arrow A D) s _ f path (lambdaRule A D body hl f bodies)

#print axioms nativeLambdaChainRealization
end LogicLineages.PersistentMarking.NativeLambdaChain
