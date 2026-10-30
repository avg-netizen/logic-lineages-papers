module
public import LogicLineages.OrdinalComparison.PeakOrbitProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualSparsePeaks : Targets.ActualSparsePeaks := actualSparsePeaks

theorem fixed_controlRootOrbitCancellation : Targets.ControlRootOrbitCancellation :=
  controlRootOrbitCancellation

theorem fixed_actualRootPeakInjectivity : Targets.ActualRootPeakInjectivity := actualRootPeakInjectivity

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
