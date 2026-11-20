module

public import LogicLineages.PersistentMarking.NumberedWindowAdmissionProgramProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowAdmissionProgramChecks
open NumberedWindowAdmissionProgramTargets

/-- The canonical encoded pair contains the window lists and input code. The encoded output
records the term and ordered-argument admission bits for that code. -/
theorem exact_AdmissionProgram : AdmissionProgram := NumberedWindowAdmissionProgramProof.program

#print axioms exact_AdmissionProgram

end LogicLineages.PersistentMarking.NumberedWindowAdmissionProgramChecks
