import LogicLineages.PersistentMarking.FreeCallProof
namespace LogicLineages.PersistentMarking.FreeCovarianceChecks

theorem shiftCancellation : FreeCovarianceTargets.ShiftCancellation := FreeShiftProof.cancellation
theorem shiftArgsCancellation : FreeCovarianceTargets.ShiftArgsCancellation := FreeShiftProof.cancellationArgs
theorem freeShift : FreeCovarianceTargets.FreeShift := FreeShiftProof.freeShift
theorem freeShiftArgs : FreeCovarianceTargets.FreeShiftArgs := FreeShiftProof.freeShiftArgs
theorem parallelComposition : FreeCovarianceTargets.ParallelComposition := FreeCompositionProof.composition
theorem parallelArgsComposition : FreeCovarianceTargets.ParallelArgsComposition := FreeCompositionProof.compositionArgs
theorem annotationPreserves : FreeCovarianceTargets.AnnotationPreserves := FreeCallProof.annotationPreserves
theorem successfulCallCovariance : FreeCovarianceTargets.SuccessfulCallCovariance := FreeCallProof.successfulCallCovariance

#print axioms shiftCancellation
#print axioms shiftArgsCancellation
#print axioms freeShift
#print axioms freeShiftArgs
#print axioms parallelComposition
#print axioms parallelArgsComposition
#print axioms annotationPreserves
#print axioms successfulCallCovariance
end LogicLineages.PersistentMarking.FreeCovarianceChecks
