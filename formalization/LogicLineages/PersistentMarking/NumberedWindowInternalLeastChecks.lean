module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLeastProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLeastChecks
open NumberedWindowInternalLeastTargets

theorem exact_LeastInterpretation : ExactLeastInterpretation :=
  NumberedWindowInternalLeastProof.interpretation

theorem exact_LeastTransport : ExactLeastTransport :=
  NumberedWindowInternalLeastProof.transport

#print axioms exact_LeastInterpretation
#print axioms exact_LeastTransport

end LogicLineages.PersistentMarking.NumberedWindowInternalLeastChecks
