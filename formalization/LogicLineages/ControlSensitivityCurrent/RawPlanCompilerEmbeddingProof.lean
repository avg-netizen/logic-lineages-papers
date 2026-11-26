module
public import LogicLineages.ControlSensitivityCurrent.RawPlanCompilerTargets
public import LogicLineages.ControlSensitivityCurrent.RawPrimitiveGateForestProof
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGOperationsStructuralProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanCompiler

open LogicLineages.OrdinalComparison.Source ExistentialPlan GroundEquivalence PrimitiveLowering
open Operations (renamingCode)
open PrimitiveGate (variable_shift_index encodePort encodeGate block_context_code)

theorem renaming_comp_codes {Γ Θ Ξ : List Ty} (r : Renaming Γ Θ) (s : Renaming Θ Ξ)
    (f : Nat → Nat) (h : ∀ {τ : Ty} (x : Variable Θ τ), variableIndex (s x) = f (variableIndex x)) :
    renamingCode (fun x => s (r x)) = (renamingCode r).map f := by
  induction Γ with
  | nil => rfl
  | cons τ Γ ih =>
      simp only [renamingCode, List.map_cons, h, ih]

theorem identity_table (Γ : List Ty) :
    renamingCode (Θ := Γ) (fun x => x) = List.range Γ.length := by
  induction Γ with
  | nil => rfl
  | cons τ Γ ih =>
      have h := renaming_comp_codes (fun {σ} (x : Variable Γ σ) => x)
        (fun {σ} (x : Variable Γ σ) => Variable.there (τ := τ) x) Nat.succ
        (fun x => rfl)
      change 0 :: renamingCode (fun x : Variable Γ _ => Variable.there (τ := τ) x) =
        List.range (Γ.length + 1)
      rw [h, ih, List.range_succ_eq_map]

theorem shifted_embedding {Γ Θ : List Ty} (r : Renaming Γ Θ) :
    renamingCode (fun x => shift 9 (r x)) = (renamingCode r).map (fun i => i + 9) :=
  renaming_comp_codes r (shift 9) _ (fun x => by
    rw [variable_shift_index, Nat.add_comm])

theorem shift_table (Γ : List Ty) :
    shiftTable (Γ.map SyntaxCode.typeCode) = renamingCode (shift 9 (Γ := Γ)) := by
  have hs := shifted_embedding (fun {τ} (x : Variable Γ τ) => x)
  rw [identity_table] at hs
  simpa only [shiftTable, List.length_map] using hs.symm

theorem renaming_tail {Γ Θ : List Ty} (r : Renaming (.ground :: Γ) Θ) :
    (renamingCode r).tail = renamingCode (fun x => r (Variable.there x)) := rfl

theorem rename_port_code {Γ Θ : List Ty} (r : Renaming Γ Θ) (p : Port Γ) :
    renamePortRaw (renamingCode r) (encodePort p) = encodePort (portRename r p) := by
  cases p with
  | zero => rfl
  | var x =>
      simp only [renamePortRaw, encodePort, portRename, Nat.add_one_ne_zero, if_false,
        Nat.add_sub_cancel, Operations.renaming_lookup]

theorem rename_gate_code {Γ Θ : List Ty} (r : Renaming Γ Θ) (g : Gate Γ) :
    renameGateRaw (renamingCode r) (encodeGate g) = encodeGate (gateRename r g) := by
  cases g <;> simp only [renameGateRaw, encodeGate, gateRename, rename_port_code] <;> rfl

theorem shift_forest_code {Γ : List Ty} (es : List (Input Γ .ground × Input Γ .ground)) :
    shiftForest (Γ.map SyntaxCode.typeCode) (RawPrimitiveGateTargets.encodeForest es) =
      RawPrimitiveGateTargets.encodeForest
        (es.map fun e => (ScopedDAG.renameInput (shift 9) e.1, ScopedDAG.renameInput (shift 9) e.2)) := by
  simp only [shiftForest, shift_table, ← block_context_code, RawPrimitiveGateTargets.encodeForest,
    List.map_map, Function.comp_def, Operations.rename_input]

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanCompiler
