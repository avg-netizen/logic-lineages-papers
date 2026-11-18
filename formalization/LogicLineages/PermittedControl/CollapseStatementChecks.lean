module
public import LogicLineages.PermittedControl.CollapseProof

public section
namespace LogicLineages.PermittedControl.StatementChecks
 theorem fixed_collapseEstimates : Targets.CollapseEstimates := collapseEstimates
 theorem fixed_singlePredecessor : Targets.SinglePredecessor := singlePredecessor
 theorem fixed_selectedControlAdmissibility : Targets.SelectedControlAdmissibility := selectedControlAdmissibility
 theorem fixed_selectedCollapseEstimates : Targets.SelectedCollapseEstimates := selectedCollapseEstimates
 theorem fixed_selectedSinglePredecessor : Targets.SelectedSinglePredecessor := selectedSinglePredecessor
#print axioms fixed_collapseEstimates
#print axioms fixed_singlePredecessor
#print axioms fixed_selectedControlAdmissibility
#print axioms fixed_selectedCollapseEstimates
#print axioms fixed_selectedSinglePredecessor
end LogicLineages.PermittedControl.StatementChecks
