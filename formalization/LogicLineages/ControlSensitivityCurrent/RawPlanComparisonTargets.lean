module
public import LogicLineages.ControlSensitivityCurrent.RawPlanComparisonDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawPlanComparisonTargets

open LogicLineages.OrdinalComparison.Source GroundEquivalence ExistentialPlan
open RawSourceDAG PlanCompiler PlanComparison

def encodeComparison {Γ : List Ty} (pair : Input Γ .ground × Input Γ .ground) : Code × Code :=
  (encode ⟨Γ,.ground,pair.1⟩, encode ⟨Γ,.ground,pair.2⟩)

def TypedExactness : Prop :=
  ∀ (Γ : List Ty) (q : Plan Γ),
    compileComparisons (Γ.map SyntaxCode.typeCode) (encodePlan q) =
      some (encodeComparison (strictPair q), encodeComparison (weakPair q))

def SuccessReconstruction : Prop :=
  ∀ (context : List Nat) (code : List Instruction) (out : OutputCode),
    compileComparisons context code = some out →
      ∃ (Γ : List Ty) (q : Plan Γ), Γ.map SyntaxCode.typeCode = context ∧ encodePlan q = code ∧
        out = (encodeComparison (strictPair q), encodeComparison (weakPair q))

def Effective : Prop :=
  Computable (fun p : List Nat × List Instruction => compileComparisons p.1 p.2)

end LogicLineages.ControlSensitivityCurrent.RawPlanComparisonTargets
