module
public import LogicLineages.ControlSensitivityCurrent.RawInputCompilerDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawInputCompilerTargets

open LogicLineages.OrdinalComparison.Source
open RawSourceDAG PlanCompiler (Instruction encodePlan)
open RawSourceDAG.InputCompiler

def TypedExactness : Prop :=
  ∀ (Γ : List Ty) (q : InputNormalization.Input Γ 0),
    run (Γ.map SyntaxCode.typeCode) (encodeInput q) =
      some (encodePlan (BooleanCompiler.lower (InputNormalization.normalize .nil q)))

def SuccessReconstruction : Prop :=
  ∀ (context : List Nat) (code : InputCode) (out : List Instruction),
    run context code = some out →
      ∃ (Γ : List Ty) (q : InputNormalization.Input Γ 0),
        Γ.map SyntaxCode.typeCode = context ∧ encodeInput q = code ∧
          out = encodePlan (BooleanCompiler.lower (InputNormalization.normalize .nil q))

def Effective : Prop :=
  Computable (fun p : List Nat × InputCode => run p.1 p.2)

end LogicLineages.ControlSensitivityCurrent.RawInputCompilerTargets
