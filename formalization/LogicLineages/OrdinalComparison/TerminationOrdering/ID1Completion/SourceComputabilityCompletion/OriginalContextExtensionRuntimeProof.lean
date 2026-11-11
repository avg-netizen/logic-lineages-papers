module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionTotalityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionRuntimeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalGraphCompositionTotalityProof InternalRecursionClosureProof
open OriginalContextExtension OriginalContextExtensionSupportProof

/-- The six witnesses arise from internal original Program totality and
existential elimination. This module does not import the native calibration
proof and does not use any native evaluation as an internal premise. -/
theorem actualOriginalContextExtensionRuntime :
    OriginalContextExtensionTargets.ActualOriginalContextExtensionRuntime := by
  intro body alpha Gamma context d lambdaObject bodyRaw psi k
  let xs : Fin 4 → OTerm alpha := ![context,d,lambdaObject,bodyRaw]
  apply supplyOutputs body 4 6 (fun i => OrdinaryArithmetic.graphFormula (runtimeQueries i))
    (fun i => (actualOriginalPrograms body 4 (runtimeQueries i)).1) alpha Gamma xs psi
  intro beta j Delta ys hj hs
  apply k beta j Delta hj (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5)
  exact recoveredFromQueries (fun a => (xs a).relabel j) ys (fun i => hs i)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionRuntimeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionRuntimeProof
