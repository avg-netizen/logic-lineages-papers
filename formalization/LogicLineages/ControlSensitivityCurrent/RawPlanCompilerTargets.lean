module
public import LogicLineages.ControlSensitivityCurrent.RawPlanCompilerDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawPlanCompilerTargets

open LogicLineages.OrdinalComparison.Source ExistentialPlan
open RawSourceDAG.PlanCompiler

def TypedExactness : Prop :=
  ∀ (Γ : List Ty) (q : Plan Γ),
    runState (Γ.map SyntaxCode.typeCode) (encodePlan q) =
      some (Γ.map SyntaxCode.typeCode, encodeResult (compile q))

def SuccessReconstruction : Prop :=
  ∀ (context : List Nat) (code : List Instruction) (out : ResultCode),
    run context code = some out →
      ∃ (Γ : List Ty) (q : Plan Γ), Γ.map SyntaxCode.typeCode = context ∧
        encodePlan q = code ∧ out = encodeResult (compile q)

def Effective : Prop :=
  Computable (fun p : List Nat × List Instruction => run p.1 p.2)

end LogicLineages.ControlSensitivityCurrent.RawPlanCompilerTargets
