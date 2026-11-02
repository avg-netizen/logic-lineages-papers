module
public import LogicLineages.OrdinalComparison.SelectedHeadCarrierTargets
public import LogicLineages.OrdinalComparison.SelectedHeadCarrierProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SelectedHeadCarrier.StatementChecks
theorem selected_activity : Targets.SelectedActivity := Proof.selectedActivity
theorem operator_extraction : Targets.OperatorExtraction := Proof.operatorExtraction
theorem actual_selected_carriers : Targets.ActualSelectedCarriers := Proof.actualSelectedCarriers
end LogicLineages.OrdinalComparison.Source.SelectedHeadCarrier.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.SelectedHeadCarrier
