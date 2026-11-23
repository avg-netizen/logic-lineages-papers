module

public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalBasisProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeOrdinalBasisChecks
open NativeOrdinalBasisTargets

theorem exact_ClosedOrdinalBasis : ClosedOrdinalBasis :=
  NativeOrdinalBasisProof.closedBasis

theorem exact_OrdinalSuccessorSteps : OrdinalSuccessorSteps :=
  NativeOrdinalBasisProof.successorSteps

theorem exact_CapAboveFiniteApplications : CapAboveFiniteApplications :=
  NativeOrdinalBasisProof.capFinite

#print axioms exact_ClosedOrdinalBasis
#print axioms exact_OrdinalSuccessorSteps
#print axioms exact_CapAboveFiniteApplications

end LogicLineages.PersistentMarking.NativeOrdinalBasisChecks
