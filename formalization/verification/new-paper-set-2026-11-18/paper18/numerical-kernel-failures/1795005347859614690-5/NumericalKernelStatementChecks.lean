module
public import LogicLineages.StandardControlCurrent.NumericalKernelProgramsProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.NumericalKernelStatementChecks
theorem full : NumericalKernelTargets.Full :=
  ⟨NumericalKernelProof.process,NumericalKernelProof.padded,NumericalKernelProof.bases,
    NumericalKernelProof.recurrence,NumericalKernelProof.programs⟩
#print axioms full
end LogicLineages.StandardControlCurrent.NumericalKernelStatementChecks
