module
public import LogicLineages.ModelsAlgebra.Forests.RankedPruneAlgorithmProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedPruneAlgorithm.StatementChecks

theorem noneExact : Targets.NoneExact := Proof.noneExact

theorem someExact : Targets.SomeExact := Proof.someExact

end LogicLineages.ModelsAlgebra.Forests.RankedPruneAlgorithm.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.RankedPruneAlgorithm
