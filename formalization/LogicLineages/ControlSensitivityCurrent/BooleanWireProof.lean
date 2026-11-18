module
public import LogicLineages.ControlSensitivityCurrent.BooleanWireTargets
public import LogicLineages.OrdinalComparison.SourceBooleanWireProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.BooleanWire
open LogicLineages.OrdinalComparison.Source
 theorem exactBooleanWires : BooleanWireTargets.ExactBooleanWires :=
  ⟨LogicLineages.OrdinalComparison.Source.BooleanWire.Proof.nodeExact, LogicLineages.OrdinalComparison.Source.BooleanWire.Proof.wireExact,
    LogicLineages.OrdinalComparison.Source.BooleanWire.Proof.uniqueWitnesses, LogicLineages.OrdinalComparison.Source.BooleanWire.Proof.rootCorrect,
    LogicLineages.OrdinalComparison.Source.BooleanWire.Proof.linearOverhead⟩
#audit_namespace LogicLineages.ControlSensitivityCurrent.BooleanWire
end LogicLineages.ControlSensitivityCurrent.BooleanWire
