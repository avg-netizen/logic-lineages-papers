module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularClosureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularClosure.StatementChecks
 theorem downwardStarExact : Targets.DownwardStarExact := Proof.downwardStarExact
 theorem compiledLinearIdeal : Targets.CompiledLinearIdeal := Proof.compiledLinearIdeal
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularClosure.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularClosure
