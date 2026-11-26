module
public import LogicLineages.ControlSensitivityCurrent.RawBinaryPlanDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawBinaryPlanTargets

open LogicLineages.OrdinalComparison.Source ExistentialPlan PrimitiveLowering SourceBinaryHalvingTrace
open RawSourceDAG PlanCompiler BinaryPlanCompiler

def TraceExactness : Prop :=
  ∀ (Γ : List Ty) (s : TraceState) (out : Port Γ) (q : Plan Γ) (pending : Nat),
    lowerTrace s (Γ.map SyntaxCode.typeCode, PrimitiveGate.encodePort out, encodePlan q, pending) =
      List.replicate pending binder ++ encodePlan (BinaryPlan.binaryPlan (reconstruct s) out q)

def ConstantExactness : Prop :=
  ∀ (Γ : List Ty) (k : Nat) (q : Plan (Ty.ground :: Γ)),
    constantRaw (Γ.map SyntaxCode.typeCode) k (encodePlan q) = encodePlan (BinaryPlan.constantPlan k q)

def Primitive : Prop :=
  Primrec (fun p : List Nat × Nat × List Instruction => constantRaw p.1 p.2.1 p.2.2)

end LogicLineages.ControlSensitivityCurrent.RawBinaryPlanTargets
