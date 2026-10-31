module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerDecisionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerDecision.StatementChecks
theorem quantifierEliminationExact : Targets.QuantifierEliminationExact := Proof.quantifierEliminationExact
theorem evaluationExact : Targets.EvaluationExact := Proof.evaluationExact
theorem closureExact : Targets.ClosureExact := Proof.closureExact
theorem satisfiabilityExact : Targets.SatisfiabilityExact := Proof.satisfiabilityExact
end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerDecision.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerDecision
