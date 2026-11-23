module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRawContextProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowRawContextChecks
open NumberedWindowRawContextTargets

theorem exact_Focus : ExactFocus := NumberedWindowRawContextFocusProof.exactFocus
theorem exact_WitnessFuel : ExactWitnessFuel := NumberedWindowRawContextFuelProof.fuelExact
theorem exact_WindowStep : ExactWindowStep := NumberedWindowRawContextProof.windowStepExact

#print axioms exact_Focus
#print axioms exact_WitnessFuel
#print axioms exact_WindowStep

end LogicLineages.PersistentMarking.NumberedWindowRawContextChecks
