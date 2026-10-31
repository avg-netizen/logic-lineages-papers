module
public import LogicLineages.ModelsAlgebra.Forests.ProfileLanguageEmptyProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ProfileLanguageEmpty.StatementChecks

theorem reachableHeightExact : Targets.ReachableHeightExact := Proof.reachableHeightExact

theorem reachableSaturation : Targets.ReachableSaturation := Proof.reachableSaturation

theorem machineEmptyCorrect : Targets.MachineEmptyCorrect := Proof.machineEmptyCorrect

theorem sourceEmptyCorrect : Targets.SourceEmptyCorrect := Proof.sourceEmptyCorrect

end LogicLineages.ModelsAlgebra.Forests.ProfileLanguageEmpty.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.ProfileLanguageEmpty
