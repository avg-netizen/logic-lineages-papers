import LogicLineages.PersistentMarking.SpineCallTypingProof
namespace LogicLineages.PersistentMarking.SpineTypingChecks

theorem annotationExact : SpineTypingTargets.AnnotationExact := SpineShiftProof.annotationExact
theorem shiftPreserves : SpineTypingTargets.ShiftPreserves := SpineShiftProof.shiftPreserves
theorem parallelPreserves : SpineTypingTargets.ParallelPreserves := SpineSubstitutionProof.parallelPreserves
theorem parallelBasePreserves : SpineTypingTargets.ParallelBasePreserves := SpineSubstitutionProof.parallelBasePreserves
theorem parallelExtrasPreserves : SpineTypingTargets.ParallelExtrasPreserves := SpineSubstitutionProof.parallelExtrasPreserves
theorem consumeExact : SpineTypingTargets.ConsumeExact := SpineCallTypingProof.consumeExact
theorem callPreserves : SpineTypingTargets.CallPreserves := SpineCallTypingProof.callPreserves
#print axioms annotationExact
#print axioms shiftPreserves
#print axioms parallelPreserves
#print axioms parallelBasePreserves
#print axioms parallelExtrasPreserves
#print axioms consumeExact
#print axioms callPreserves
end LogicLineages.PersistentMarking.SpineTypingChecks
