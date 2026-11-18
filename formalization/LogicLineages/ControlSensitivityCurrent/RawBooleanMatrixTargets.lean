module
public import LogicLineages.ControlSensitivityCurrent.RawBooleanMatrixDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawBooleanMatrixTargets

open LogicLineages.OrdinalComparison.Source PrimitiveLowering
open RawSourceDAG PlanCompiler BooleanMatrix

def TypedExactness : Prop :=
  ∀ (Γ : List Ty) (n m : Nat) (d : BooleanWire.Dag n m) (a : Fin n → Port Γ) (root : Fin m),
    matrixRaw (List.ofFn (fun j => PrimitiveGate.encodePort (a j))) (encodeRows d) root.val =
      encodePlan (BooleanPlan.matrixPlan d a root)

def Primitive : Prop :=
  Primrec (fun p : List Nat × List RowCode × Nat => matrixRaw p.1 p.2.1 p.2.2)

end LogicLineages.ControlSensitivityCurrent.RawBooleanMatrixTargets
