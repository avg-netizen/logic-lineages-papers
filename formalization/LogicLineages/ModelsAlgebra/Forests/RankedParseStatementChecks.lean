module
public import LogicLineages.ModelsAlgebra.Forests.RankedParseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedParse.StatementChecks

theorem homeomorphicInduced : Targets.HomeomorphicInduced :=
  Proof.homeomorphicInduced

theorem exactPruning : Targets.ExactPruning :=
  Proof.exactPruning

end LogicLineages.ModelsAlgebra.Forests.RankedParse.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.RankedParse
