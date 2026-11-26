module
public import LogicLineages.PermittedControl.ActualTraceSignCutoffTargets
import LogicLineages.PermittedControl.ActualTraceSignCutoffProof

@[expose] public section
namespace LogicLineages.PermittedControl.StatementChecks

theorem fixed_actualTraceSignCutoff :
    ActualTraceSignCutoff.FullActualTraceSignCutoff :=
  ActualTraceSignCutoff.fullActualTraceSignCutoff

#print axioms fixed_actualTraceSignCutoff

end LogicLineages.PermittedControl.StatementChecks
