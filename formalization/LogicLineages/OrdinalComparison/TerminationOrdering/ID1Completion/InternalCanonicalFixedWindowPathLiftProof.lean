module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowPathLiftCompatibilityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowPathLiftEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowPathLiftProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open InternalCanonicalFixedWindowVertexDispatch
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualInternalCanonicalFixedWindowEdgeCompatibility :
    InternalCanonicalFixedWindowPathLiftTargets.ActualInternalCanonicalFixedWindowEdgeCompatibility :=
  InternalCanonicalFixedWindowPathLiftCompatibilityProof.actualInternalCanonicalFixedWindowEdgeCompatibility

theorem actualInternalCanonicalFixedWindowReflexivePathLift :
    InternalCanonicalFixedWindowPathLiftTargets.ActualInternalCanonicalFixedWindowReflexivePathLift := by
  intro S data hm hc window oldVertex body sigma tau
  exact InternalApplicationPathLiftProof.actualInternalReflexivePathLift body
    (InternalCanonicalQuotientEdgeSelection.edgeChecker data)
    (vertex window data oldVertex) (invariant window data sigma tau)
    (InternalCanonicalFixedWindowVertexDispatchProof.actualInternalCanonicalFixedWindowInvariantPreservation
      window data body sigma tau)
    (actualInternalCanonicalFixedWindowEdgeCompatibility
      S data hm hc window oldVertex body sigma tau)

theorem actualInternalCanonicalFixedWindowPositivePathLift :
    InternalCanonicalFixedWindowPathLiftTargets.ActualInternalCanonicalFixedWindowPositivePathLift := by
  intro S data hm hc window oldVertex body sigma tau
  exact InternalApplicationPathLiftProof.actualInternalPositivePathLift body
    (InternalCanonicalQuotientEdgeSelection.edgeChecker data)
    (vertex window data oldVertex) (invariant window data sigma tau)
    (InternalCanonicalFixedWindowVertexDispatchProof.actualInternalCanonicalFixedWindowInvariantPreservation
      window data body sigma tau)
    (actualInternalCanonicalFixedWindowEdgeCompatibility
      S data hm hc window oldVertex body sigma tau)

theorem actualOriginalCanonicalFixedWindowLiftPathCalibration :
    InternalCanonicalFixedWindowPathLiftTargets.ActualOriginalCanonicalFixedWindowLiftPathCalibration :=
  InternalCanonicalFixedWindowPathLiftEvaluationProof.actualOriginalCanonicalFixedWindowLiftPathCalibration

theorem actualOriginalCanonicalFixedWindowDecodedPathValue :
    InternalCanonicalFixedWindowPathLiftTargets.ActualOriginalCanonicalFixedWindowDecodedPathValue :=
  InternalCanonicalFixedWindowPathLiftEvaluationProof.actualOriginalCanonicalFixedWindowDecodedPathValue

/-- Select once using the vertex package. Its SAME Data supplies the member
calibration for every application/path law, before all closed type and term
quantifiers. No unrelated existential application witness is substituted. -/
theorem actualOriginalSelectedCanonicalFixedWindowPathLift :
    InternalCanonicalFixedWindowPathLiftTargets.ActualOriginalSelectedCanonicalFixedWindowPathLift := by
  intro n arity symbols S Gamma table hc
  obtain ⟨data,oldVertex,hd,hs,hedge,hold,hvertex,hdispatch,hinvariant⟩ :=
    InternalCanonicalFixedWindowVertexDispatchProof.actualOriginalCanonicalFixedWindowVertexSelection
      n arity symbols S Gamma table hc
  refine ⟨data,oldVertex,hd,hs,
    InternalCanonicalQuotientEdgeApplicationLiftProof.actualOriginalCanonicalApplicationCalibration
      n arity symbols S Gamma table data hc hd,
    hedge,?_,hold,hvertex,
    actualOriginalCanonicalFixedWindowLiftPathCalibration
      n arity symbols S Gamma table data oldVertex hc hd hold,
    actualOriginalCanonicalFixedWindowDecodedPathValue
      n arity symbols S Gamma table data oldVertex hc hd hold,
    hdispatch,hinvariant,?_⟩
  · intro body sigma tau α Delta
    exact ⟨InternalCanonicalQuotientEdgeApplicationLiftProof.actualOriginalCanonicalApplicationTypedOutput
        S data hd.2.1 hc body sigma tau α Delta,
      InternalCanonicalQuotientEdgeApplicationLiftProof.actualOriginalCanonicalQuotientEdgeApplicationLift
        S data hd.2.1 hc body sigma tau α Delta,
      InternalCanonicalQuotientEdgeApplicationLiftProof.actualOriginalCanonicalQuotientEdgeApplicationTypedOutputs
        S data hd.2.1 hc body sigma tau α Delta⟩
  · intro body sigma tau
    refine ⟨actualInternalCanonicalFixedWindowEdgeCompatibility S data hd.2.1 hc
      (OrdinaryArithmeticQuotient.contextCode symbols S table) oldVertex body sigma tau,?_⟩
    intro α Delta ps x y certificate out other mapped
    exact ⟨actualInternalCanonicalFixedWindowReflexivePathLift S data hd.2.1 hc
        (OrdinaryArithmeticQuotient.contextCode symbols S table) oldVertex body sigma tau
        α Delta ps x y certificate out other mapped,
      actualInternalCanonicalFixedWindowPositivePathLift S data hd.2.1 hc
        (OrdinaryArithmeticQuotient.contextCode symbols S table) oldVertex body sigma tau
        α Delta ps x y certificate out other mapped⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowPathLiftProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowPathLiftProof
