module
public import LogicLineages.ControlSensitivityCurrent.RawPlanCompilerTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanCompiler

/-- Use the canonical sum encoding at the concrete instruction universe. -/
instance instructionPrimcodable : Primcodable Instruction :=
  @Primcodable.sum (Code × Code) (PrimitiveGate.GateCode ⊕ (PUnit : Type)) inferInstance
    (@Primcodable.sum PrimitiveGate.GateCode (PUnit : Type) inferInstance Primcodable.unit)

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanCompiler
