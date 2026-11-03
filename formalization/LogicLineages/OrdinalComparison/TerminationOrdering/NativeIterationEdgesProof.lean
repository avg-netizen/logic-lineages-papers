module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NativeIterationEdgesSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NativeIterationEdgesProof
open Source NativeCarrier NativeIterationEdges NativeIterationEdgesSupportProof

theorem baseEdge : NativeIterationEdgesTargets.BaseEdge := by
  intro Symbol arity above A P U i
  exact NativeCarrierProof.baseStrict Symbol arity above (translatedType A) (step A P i) U

theorem indexEdge : NativeIterationEdgesTargets.IndexEdge := by
  intro Symbol arity above A P U i j h
  exact carrierMonotonicity above (step A P i) (step A P j) U (stepMonotonicity above A P i j h)

theorem applicationEdge : NativeIterationEdgesTargets.ApplicationEdge := by
  intro Symbol arity above A P U i j h
  exact NativeCarrierProof.applicationClosure Symbol arity above (translatedType A) P (step A P i) U
    (iterationCarrier A P U j) (stepProjection above A P i) (indexEdge Symbol arity above A P U i j h)

end LogicLineages.OrdinalComparison.TerminationOrdering.NativeIterationEdgesProof
