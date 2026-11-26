module
public import LogicLineages.OrdinalComparison.SourceBooleanWireTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.BooleanWireTargets
open LogicLineages.OrdinalComparison.Source
/-- Supporting literal six-node Boolean DAG semantics; no source-language coverage claim. -/
def ExactBooleanWires : Prop := BooleanWire.Targets.NodeExact ∧
  BooleanWire.Targets.WireExact ∧ BooleanWire.Targets.UniqueWitnesses ∧
  BooleanWire.Targets.RootCorrect ∧ BooleanWire.Targets.LinearOverhead
end LogicLineages.ControlSensitivityCurrent.BooleanWireTargets
