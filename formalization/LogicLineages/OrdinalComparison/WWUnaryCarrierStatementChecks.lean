module
public import LogicLineages.OrdinalComparison.WWUnaryCarrierProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnaryCarrier.StatementChecks
 theorem freshRename : Targets.FreshRename := Proof.freshRename
 theorem saturation : Targets.Saturation := Proof.saturation
 theorem captureClosing : Targets.CaptureClosing := Proof.captureClosing
 theorem actualCarrier : Targets.ActualCarrier := Proof.actualCarrier
end LogicLineages.OrdinalComparison.Source.UnaryCarrier.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.UnaryCarrier
