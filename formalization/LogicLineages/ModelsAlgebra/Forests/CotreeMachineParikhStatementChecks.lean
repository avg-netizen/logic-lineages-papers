module
public import LogicLineages.ModelsAlgebra.Forests.CotreeMachineParikhProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeMachineParikh.StatementChecks

theorem stateTransitionExact : Targets.StateTransitionExact := Proof.stateTransitionExact

theorem tableTransitionExact : Targets.TableTransitionExact := Proof.tableTransitionExact

theorem encodingRunExact : Targets.EncodingRunExact := Proof.encodingRunExact

theorem numberedTransitionExact : Targets.NumberedTransitionExact := Proof.numberedTransitionExact

end LogicLineages.ModelsAlgebra.Forests.CotreeMachineParikh.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreeMachineParikh
