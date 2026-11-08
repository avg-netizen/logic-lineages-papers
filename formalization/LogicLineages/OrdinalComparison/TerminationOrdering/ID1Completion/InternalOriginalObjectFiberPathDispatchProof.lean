module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchGraphProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowPathLiftProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftPathPrimitiveProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchProof
open InternalOriginalObjectFiberPathDispatch

theorem actualOriginalObjectFiberCodec :
    InternalOriginalObjectFiberPathDispatchTargets.ActualOriginalObjectFiberCodec :=
  InternalOriginalObjectFiberPathDispatchEvaluationProof.actualOriginalObjectFiberCodec

theorem actualOriginalObjectFiberDispatchEvaluation :
    InternalOriginalObjectFiberPathDispatchTargets.ActualOriginalObjectFiberDispatchEvaluation :=
  InternalOriginalObjectFiberPathDispatchEvaluationProof.actualOriginalObjectFiberDispatchEvaluation

theorem actualOriginalObjectFiberPathValueCalibration :
    InternalOriginalObjectFiberPathDispatchTargets.ActualOriginalObjectFiberPathValueCalibration :=
  InternalOriginalObjectFiberPathDispatchEvaluationProof.actualOriginalObjectFiberPathValueCalibration

theorem actualInternalOriginalObjectFiberPairGraph :
    InternalOriginalObjectFiberPathDispatchTargets.ActualInternalOriginalObjectFiberPairGraph :=
  InternalOriginalObjectFiberPathDispatchGraphProof.actualInternalOriginalObjectFiberPairGraph

theorem actualInternalOriginalObjectFiberActiveGraph :
    InternalOriginalObjectFiberPathDispatchTargets.ActualInternalOriginalObjectFiberActiveGraph :=
  InternalOriginalObjectFiberPathDispatchGraphProof.actualInternalOriginalObjectFiberActiveGraph

theorem actualInternalOriginalObjectFiberZeroGraph :
    InternalOriginalObjectFiberPathDispatchTargets.ActualInternalOriginalObjectFiberZeroGraph :=
  InternalOriginalObjectFiberPathDispatchGraphProof.actualInternalOriginalObjectFiberZeroGraph

theorem actualInternalOriginalObjectFiberNonmatchGraph :
    InternalOriginalObjectFiberPathDispatchTargets.ActualInternalOriginalObjectFiberNonmatchGraph :=
  InternalOriginalObjectFiberPathDispatchGraphProof.actualInternalOriginalObjectFiberNonmatchGraph

/-- The previous selected package is used ONCE, retaining its SAME Data,
oldVertex, window and Gamma. Select the original global oldLift once; the
new internal graph laws hold uniformly before bodies and symbolic inputs. -/
theorem actualOriginalSelectedObjectFiberPathDispatch :
    InternalOriginalObjectFiberPathDispatchTargets.ActualOriginalSelectedObjectFiberPathDispatch := by
  intro n arity symbols S Gamma table hc
  obtain ⟨data,oldVertex,hd,hs,happ,he,hal,ho,hv,hp,hdec,hvL,hi,hpL⟩ :=
    InternalCanonicalFixedWindowPathLiftProof.actualOriginalSelectedCanonicalFixedWindowPathLift
      n arity symbols S Gamma table hc
  obtain ⟨oldLift,hold⟩ := ApplicationCertificateLiftPathPrimitiveProof.actualProgramWitness n arity
  refine ⟨data,oldVertex,oldLift,hd,hs,happ,he,hal,ho,hv,hp,hdec,hvL,hi,hpL,hold,
    actualOriginalObjectFiberPathValueCalibration n arity symbols S Gamma table
      data oldVertex oldLift hc hd ho hold,?_⟩
  intro body α Delta
  let vertexProgram := InternalCanonicalFixedWindowVertexDispatch.vertex
    (OrdinaryArithmeticQuotient.contextCode symbols S table) data oldVertex
  exact ⟨actualInternalOriginalObjectFiberPairGraph Gamma body α Delta,
    actualInternalOriginalObjectFiberActiveGraph Gamma vertexProgram oldLift body α Delta,
    actualInternalOriginalObjectFiberZeroGraph Gamma vertexProgram oldLift body α Delta,
    actualInternalOriginalObjectFiberNonmatchGraph Gamma vertexProgram oldLift body α Delta⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchProof
