module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerExecutableProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerExecutable.StatementChecks
theorem queryExact : Targets.QueryExact := Proof.queryExact
theorem enabledExact : Targets.EnabledExact := Proof.enabledExact
theorem reachableExact : Targets.ReachableExact := Proof.reachableExact
theorem productiveExact : Targets.ProductiveExact := Proof.productiveExact
theorem sourceEmptyExact : Targets.SourceEmptyExact := Proof.sourceEmptyExact
theorem sourceInclusionExact : Targets.SourceInclusionExact := Proof.sourceInclusionExact
end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerExecutable.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerExecutable
