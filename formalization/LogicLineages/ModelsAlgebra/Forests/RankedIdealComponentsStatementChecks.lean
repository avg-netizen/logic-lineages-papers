module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealComponentsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealComponents.StatementChecks
 theorem reachLanguageInclusion : Targets.ReachLanguageInclusion := Proof.reachLanguageInclusion
 theorem componentLanguageEquality : Targets.ComponentLanguageEquality := Proof.componentLanguageEquality
 theorem stateLanguageDownward : Targets.StateLanguageDownward := Proof.stateLanguageDownward
 theorem nonlinearIdeal : Targets.NonlinearIdeal := Proof.nonlinearIdeal
end LogicLineages.ModelsAlgebra.Forests.RankedIdealComponents.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealComponents
