module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularStateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularState.StatementChecks
 theorem stateLanguageExact : Targets.StateLanguageExact := Proof.stateLanguageExact
 theorem compiledNonlinearIdeal : Targets.CompiledNonlinearIdeal := Proof.compiledNonlinearIdeal
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularState.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularState
