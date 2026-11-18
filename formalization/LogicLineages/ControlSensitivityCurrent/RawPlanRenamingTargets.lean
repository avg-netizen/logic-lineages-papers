module
public import LogicLineages.ControlSensitivityCurrent.RawPlanRenamingDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawPlanRenamingTargets

open LogicLineages.OrdinalComparison.Source ExistentialPlan
open RawSourceDAG PlanCompiler PlanRenaming

def TypedExactness : Prop :=
  ∀ (Γ Θ : List Ty) (r : Renaming Γ Θ) (q : Plan Γ),
    renamePlanRaw (Θ.map SyntaxCode.typeCode) (Operations.renamingCode r) (encodePlan q) =
      encodePlan (BinaryPlan.renamePlan r q)

def Primitive : Prop :=
  Primrec (fun p : List Nat × List Nat × List Instruction => renamePlanRaw p.1 p.2.1 p.2.2)

end LogicLineages.ControlSensitivityCurrent.RawPlanRenamingTargets
