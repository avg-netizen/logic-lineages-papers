module
public import LogicLineages.ModelsAlgebra.Forests.ForestParikhTransitionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParikhTransition.StatementChecks

theorem stateSetTransport : Targets.StateSetTransport := Proof.stateSetTransport

theorem childCountTransport : Targets.ChildCountTransport := Proof.childCountTransport

theorem numberedParikhExact : Targets.NumberedParikhExact := Proof.numberedParikhExact

theorem semanticCompleteness : Targets.SemanticCompleteness := Proof.semanticCompleteness

end LogicLineages.ModelsAlgebra.Forests.ForestParikhTransition.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.ForestParikhTransition
