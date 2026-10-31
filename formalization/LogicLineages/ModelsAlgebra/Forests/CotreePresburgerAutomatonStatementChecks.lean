module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerAutomatonProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerAutomaton.StatementChecks

theorem nodeStepExact : Targets.NodeStepExact := Proof.nodeStepExact

theorem runsExact : Targets.RunsExact := Proof.runsExact

theorem runsDeterministic : Targets.RunsDeterministic := Proof.runsDeterministic

theorem acceptanceExact : Targets.AcceptanceExact := Proof.acceptanceExact

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerAutomaton.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerAutomaton
