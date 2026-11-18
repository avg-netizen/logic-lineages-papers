module
public import LogicLineages.ControlSensitivityCurrent.RawInputCompilerSourceProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler

open LogicLineages.OrdinalComparison.Source PrimitiveLowering GroundEquivalence
open BinaryPlanCompiler (binder gate shiftPort)
open BooleanMatrix (addCode)
open PrimitiveGate (encodePort port_guard_typed)

theorem run_from_cons {s t : InputState} {i : InputStep} (h : advance s i = some t) (rest : InputCode) :
    runFrom s (prependStep i rest) = runFrom t rest := by
  simp only [runFrom, prependStep, List.foldl_cons, Option.bind_some, h]

theorem advance_boolean {Γ : List Ty} {m : Nat} (d : InputNormalization.Dag Γ m)
    (row : InputNormalization.Node Γ m) (pending : List Lowering) :
    advance (stateOf d pending) (encodeInputRow row,none) =
      some (stateOf (.snoc d row) pending) := by
  rw [← add_row_state]
  cases row <;> simp [advance, encodeInputRow, booleanGuard, stateOf,
    BooleanMatrix.encode_rows_length, port_guard_typed, Fin.isLt]

theorem advance_add {Γ : List Ty} {m : Nat} (d : InputNormalization.Dag Γ m)
    (a b : Port Γ) (pending : List Lowering) :
    advance (stateOf d pending) ((6,encodePort a,encodePort b),none) =
      some (stateOf (d.rename (Renaming.weaken Γ .ground))
        (([binder,gate (addCode (shiftPort 1 (encodePort a)) (shiftPort 1 (encodePort b)) 1)],[],none)::pending)) := by
  rw [← add_wire_state]
  simp [advance, stateOf, port_guard_typed]

theorem advance_literal {Γ : List Ty} {m : Nat} (d : InputNormalization.Dag Γ m)
    (k : Nat) (pending : List Lowering) :
    advance (stateOf d pending) ((7,k,0),none) =
      some (stateOf (d.rename (Renaming.weaken Γ .ground))
        (([],Γ.map SyntaxCode.typeCode,some k)::pending)) := by
  rw [← add_wire_state]
  rfl

theorem advance_observation {Γ : List Ty} {m : Nat} (d : InputNormalization.Dag Γ m)
    (t : Input Γ .ground) (pending : List Lowering) :
    advance (stateOf d pending) ((8,0,0),some (encode ⟨Γ,.ground,t⟩)) =
      some (stateOf (d.rename (Renaming.weaken Γ .ground))
        ((equationChunk (Γ.map SyntaxCode.typeCode) (encode ⟨Γ,.ground,t⟩),[],none)::pending)) := by
  have hg : inputDAGGuard (Γ.map SyntaxCode.typeCode) 0 (encode ⟨Γ,.ground,t⟩) = true :=
    typed_dag_guard ⟨Γ,.ground,t⟩
  rw [← add_wire_state]
  simp [advance, stateOf, hg]

theorem advance_unary {Γ : List Ty} {m : Nat} (d : InputNormalization.Dag Γ m)
    (h : Input [] (.arrow .ground .ground)) (x : Variable Γ .ground) (pending : List Lowering) :
    advance (stateOf d pending) ((9,variableIndex x,0),some (encode ⟨[],.arrow .ground .ground,h⟩)) =
      some (stateOf (d.rename (Renaming.weaken Γ .ground))
        ((equationChunk (Γ.map SyntaxCode.typeCode) (encode ⟨Γ,.ground,BooleanCompiler.call h x⟩),[],none)::pending)) := by
  have hg : inputDAGGuard [] (SyntaxCode.arrowCode 0 0) (encode ⟨[],.arrow .ground .ground,h⟩) = true :=
    typed_dag_guard ⟨[],.arrow .ground .ground,h⟩
  rw [← add_wire_state]
  simp [advance, stateOf, hg, typed_variable_guard, unary_call_exact]

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler
