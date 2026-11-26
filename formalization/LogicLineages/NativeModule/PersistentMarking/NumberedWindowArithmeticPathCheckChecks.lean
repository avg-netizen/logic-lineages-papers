module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticPathClassProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticPathPrimaryProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticPathCheckChecks
open NumberedWindowArithmeticPathCheckTargets

theorem exact_WindowStepOnCodes : ExactWindowStepOnCodes :=
  NumberedWindowArithmeticPathWindowProof.step

theorem exact_WindowPathOnCodes : ExactWindowPathOnCodes :=
  NumberedWindowArithmeticPathWindowProof.path

theorem exact_ClassEdgeOnCodes : ExactClassEdgeOnCodes :=
  NumberedWindowArithmeticPathClassProof.edge

theorem exact_PositiveClassPathOnCodes : ExactPositiveClassPathOnCodes :=
  NumberedWindowArithmeticPathClassProof.path

theorem exact_PrimaryOnCodes : ExactPrimaryOnCodes :=
  NumberedWindowArithmeticPathPrimaryProof.primary

theorem exact_CodedChecksRejectMalformed : CodedChecksRejectMalformed :=
  NumberedWindowArithmeticPathPrimaryProof.malformed

#print axioms exact_WindowStepOnCodes
#print axioms exact_WindowPathOnCodes
#print axioms exact_ClassEdgeOnCodes
#print axioms exact_PositiveClassPathOnCodes
#print axioms exact_PrimaryOnCodes
#print axioms exact_CodedChecksRejectMalformed

end LogicLineages.PersistentMarking.NumberedWindowArithmeticPathCheckChecks
