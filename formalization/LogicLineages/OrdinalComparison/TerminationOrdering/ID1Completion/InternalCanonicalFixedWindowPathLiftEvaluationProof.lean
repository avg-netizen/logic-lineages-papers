module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowPathLiftTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathMapEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowPathLiftEvaluationProof
open InternalCanonicalFixedWindowVertexDispatch

/-- The accepted dispatched vertex calibration feeds the original path mapper
on every natural five-vector, retaining the raw argument and original edges. -/
theorem actualOriginalCanonicalFixedWindowLiftPathCalibration :
    InternalCanonicalFixedWindowPathLiftTargets.ActualOriginalCanonicalFixedWindowLiftPathCalibration := by
  intro n arity symbols S Gamma table data oldVertex hc hdata hold
  exact InternalApplicationPathMapEvaluationProof.actualOriginalPathCalibration
    n arity Gamma
    (vertex (OrdinaryArithmeticQuotient.contextCode symbols S table) data oldVertex)
    (InternalCanonicalFixedWindowVertexDispatchProof.actualOriginalCanonicalFixedWindowVertexCalibration
      n arity symbols S Gamma table data oldVertex hc hdata hold)

/-- Decode only the original argument object, then use the same fixed-Gamma
all-input calibration with its unmodified raw payload. -/
theorem actualOriginalCanonicalFixedWindowDecodedPathValue :
    InternalCanonicalFixedWindowPathLiftTargets.ActualOriginalCanonicalFixedWindowDecodedPathValue := by
  intro n arity symbols S Gamma table data oldVertex hc hdata hold
    context domain codomain argumentObject argument certificate hdecode
  unfold ApplicationCertificateLiftPath.pathValue
  change _ = ((Encodable.decode (α := ContextUniform.Object) argumentObject).map
    (fun a => ApplicationCertificateLiftPath.liftPath n arity a.1
      context domain codomain a.2 certificate)).getD 0
  rw [hdecode]
  exact actualOriginalCanonicalFixedWindowLiftPathCalibration
    n arity symbols S Gamma table data oldVertex hc hdata hold
    (List.Vector.ofFn ![certificate,context,domain,codomain,argument])

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowPathLiftEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowPathLiftEvaluationProof
