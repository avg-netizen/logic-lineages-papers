module
public import LogicLineages.ControlSensitivityCurrent.RawInputCompilerStateProof
public import LogicLineages.ControlSensitivityCurrent.RawCheckedCompositionTypedProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler

open LogicLineages.OrdinalComparison.Source ExistentialPlan PrimitiveLowering GroundEquivalence
open BinaryPlanCompiler (binder gate shiftPort prefixTable shift_port_code prefix_table_code)
open BooleanMatrix (addCode)
open PrimitiveGate (encodePort portRaw port_guard_typed)
open PlanCompiler (Instruction encodePlan)

theorem boolean_guard_typed {Γ : List Ty} {m : Nat} (row : InputNormalization.Node Γ m) :
    booleanGuard (Γ.map SyntaxCode.typeCode) m (encodeInputRow row) = true := by
  cases row <;> simp [booleanGuard, encodeInputRow, port_guard_typed, Fin.isLt]

theorem typed_dag_guard (d : Packed) :
    inputDAGGuard (d.1.map SyntaxCode.typeCode) (SyntaxCode.typeCode d.2.1) (encode d) = true := by
  rw [inputDAGGuard, typedAccepted]
  simp [encode]

theorem typed_variable_guard {Γ : List Ty} (x : Variable Γ .ground) :
    RawValidator.«variable» (Γ.map SyntaxCode.typeCode) 0 (variableIndex x) = true := by
  have h := RawValidator.variable_status Γ Ty.ground (variableIndex x)
  rw [variable_roundtrip] at h
  exact h

theorem equation_chunk_exact {Γ : List Ty} (d : Input Γ .ground) (tail : Plan (.ground :: Γ)) :
    equationChunk (Γ.map SyntaxCode.typeCode) (encode ⟨Γ,.ground,d⟩) ++ encodePlan tail =
      encodePlan (.existsGround (.equation
        (ScopedDAG.renameInput (Renaming.weaken Γ .ground) d) (ScopedDAG.variableInput .here) tail)) := by
  have h : Operations.renameCode (0 :: Γ.map SyntaxCode.typeCode) (Operations.renamingCode (shift 1 (Γ := Γ)))
      (encode ⟨Γ,.ground,d⟩) =
        encode ⟨.ground :: Γ,.ground,ScopedDAG.renameInput (Renaming.weaken Γ .ground) d⟩ :=
    (Operations.rename_input (Renaming.weaken Γ .ground) d).symm
  simp only [equationChunk, prefix_table_code, h]
  rfl

theorem unary_call_exact {Γ : List Ty} (h : Input [] (.arrow .ground .ground))
    (x : Variable Γ .ground) :
    unaryCallRaw (Γ.map SyntaxCode.typeCode) (encode ⟨[],.arrow .ground .ground,h⟩) (variableIndex x) =
      encode ⟨Γ,.ground,BooleanCompiler.call h x⟩ := by
  have hr := Operations.rename_input (BooleanCompiler.emptyRename Γ) h
  change encode ⟨Γ,.arrow .ground .ground,ScopedDAG.renameInput (BooleanCompiler.emptyRename Γ) h⟩ =
    Operations.renameCode (Γ.map SyntaxCode.typeCode) [] (encode ⟨[],.arrow .ground .ground,h⟩) at hr
  have hx : portRaw (Γ.map SyntaxCode.typeCode) (variableIndex x+1) =
      encode ⟨Γ,.ground,ScopedDAG.variableInput x⟩ := rfl
  rw [unaryCallRaw, ← hr, hx]
  exact CheckedComposition.application_raw_exact _ _

theorem addition_chunk_exact {Γ : List Ty} (a b : Port Γ) (tail : Plan (.ground :: Γ)) :
    [binder,gate (addCode (shiftPort 1 (encodePort a)) (shiftPort 1 (encodePort b)) 1)] ++ encodePlan tail =
      encodePlan (.existsGround (.gate
        (.add (portRename (Renaming.weaken Γ .ground) a)
          (portRename (Renaming.weaken Γ .ground) b) (.var .here)) tail)) := by
  rw [shift_port_code, shift_port_code]
  rfl

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler
