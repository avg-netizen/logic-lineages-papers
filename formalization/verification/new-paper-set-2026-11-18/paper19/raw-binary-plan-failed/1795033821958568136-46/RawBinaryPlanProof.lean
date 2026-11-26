module
public import LogicLineages.ControlSensitivityCurrent.RawBinaryPlanTargets
public import LogicLineages.ControlSensitivityCurrent.RawPlanRenamingProof
public import LogicLineages.ControlSensitivityCurrent.BinaryGeneratorProof
public import Mathlib.Data.List.Induction
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.BinaryPlanCompiler

open LogicLineages.OrdinalComparison.Source ExistentialPlan PrimitiveLowering
open SourceAdditionCompletion SourceBinaryHalvingTrace
open PlanCompiler (encodePlan identity_table renaming_comp_codes)
open PrimitiveGate (encodePort encodeGate variable_shift_index)
open Operations (renamingCode)

theorem prefix_table_code (Γ : List Ty) (n : Nat) :
    prefixTable n (Γ.map SyntaxCode.typeCode) = renamingCode (shift n (Γ := Γ)) := by
  have h := renaming_comp_codes (fun {τ} (x : Variable Γ τ) => x) (shift n)
    (fun i => i + n) (fun x => by rw [variable_shift_index, Nat.add_comm])
  rw [identity_table] at h
  simpa only [prefixTable, List.length_map] using h.symm

theorem shift_port_code {Γ : List Ty} (n : Nat) (p : Port Γ) :
    shiftPort n (encodePort p) = encodePort (portRename (shift n) p) := by
  cases p with
  | zero => rfl
  | var x =>
      simp only [shiftPort, encodePort, Nat.add_one_ne_zero, if_false, portRename, variable_shift_index]
      omega

private theorem trace_step (base : Nat) (bits : List Nat) (b : Nat) (init : BinaryState) :
    lowerTrace (base,bits ++ [b]) init = lowerTrace (base,bits) (binaryStep init b) := by
  simp [lowerTrace, List.reverse_append, List.foldl_cons]

private theorem reconstruct_step (base : Nat) (bits : List Nat) (b : Nat) :
    reconstruct (base,bits ++ [b]) = wrap (reconstruct (base,bits)) b := by
  simp [reconstruct, List.foldl_append]

theorem trace_exactness : RawBinaryPlanTargets.TraceExactness := by
  intro Γ s out q pending
  rcases s with ⟨base,bits⟩
  induction bits using List.reverseRecOn generalizing Γ out q pending with
  | nil => by_cases hb : base = 0 <;>
      simp [lowerTrace, finish, reconstruct, hb, BinaryPlan.binaryPlan, encodePlan, encodeGate, gate] <;> rfl
  | append_singleton bits bit ih =>
      rw [trace_step, reconstruct_step]
      by_cases hb : bit = 0
      · let stepTail : Plan (.ground :: Γ) :=
          .gate (.add (.var .here) (.var .here) (portRename (shift 1) out))
            (BinaryPlan.renamePlan (shift 1) q)
        have hr := PlanRenaming.typed_exactness Γ (.ground :: Γ) (shift 1) q
        have hstep : binaryStep (Γ.map SyntaxCode.typeCode,encodePort out,encodePlan q,pending) bit =
            ((Ty.ground :: Γ).map SyntaxCode.typeCode,1,encodePlan stepTail,pending+1) := by
          simp only [binaryStep, hb, ite_true, prefix_table_code, shift_port_code, stepTail, encodePlan,
            encodeGate, gate]
          rw [← hr]
          rfl
        rw [hstep]
        change lowerTrace (base,bits) ((Ty.ground :: Γ).map SyntaxCode.typeCode,
          encodePort (.var .here : Port (.ground :: Γ)),encodePlan stepTail,pending+1) = _
        rw [ih]
        simp [wrap, hb, BinaryPlan.binaryPlan, encodePlan, binder, List.replicate_add,
          stepTail, Renaming.weaken, shift, List.append_assoc]
      · let stepTail : Plan (.ground :: .ground :: .ground :: Γ) :=
          .gate (.add (.var (.there (.there .here))) (.var (.there (.there .here))) (.var (.there .here)))
            (.gate (.one (.var .here))
              (.gate (.add (.var (.there .here)) (.var .here) (portRename (shift 3) out))
                (BinaryPlan.renamePlan (shift 3) q)))
        have hr := PlanRenaming.typed_exactness Γ (.ground :: .ground :: .ground :: Γ) (shift 3) q
        have hstep : binaryStep (Γ.map SyntaxCode.typeCode,encodePort out,encodePlan q,pending) bit =
            ((Ty.ground :: Ty.ground :: Ty.ground :: Γ).map SyntaxCode.typeCode,3,encodePlan stepTail,pending+3) := by
          simp only [binaryStep, hb, ite_false, prefix_table_code, shift_port_code, stepTail, encodePlan,
            encodeGate, gate]
          rw [← hr]
          rfl
        rw [hstep]
        change lowerTrace (base,bits) ((Ty.ground :: Ty.ground :: Ty.ground :: Γ).map SyntaxCode.typeCode,
          encodePort (.var (.there (.there .here)) : Port (.ground :: .ground :: .ground :: Γ)),encodePlan stepTail,pending+3) = _
        rw [ih]
        simp [wrap, hb, BinaryPlan.binaryPlan, encodePlan, binder, List.replicate_add,
          stepTail, List.append_assoc]

theorem constant_exactness : RawBinaryPlanTargets.ConstantExactness := by
  intro Γ k q
  change lowerTrace (trace k) ((Ty.ground :: Γ).map SyntaxCode.typeCode,
    encodePort (.var .here : Port (.ground :: Γ)), encodePlan q, 1) = _
  rw [trace_exactness, BinaryGenerator.exactReconstruction]
  rfl

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.BinaryPlanCompiler
