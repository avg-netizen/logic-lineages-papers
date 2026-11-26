module
public import LogicLineages.ControlSensitivityCurrent.RawInputCompilerTargets
public import LogicLineages.ControlSensitivityCurrent.RawBinaryPlanProof
public import LogicLineages.ControlSensitivityCurrent.RawBooleanMatrixProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler

open LogicLineages.OrdinalComparison.Source PrimitiveLowering
open InputNormalization (Dag arity)
open PrimitiveGate (encodePort)
open BooleanMatrix (encodeRow encodeRows)
open BinaryPlanCompiler (shiftPort shift_port_code)

def encodedPorts {Γ : List Ty} {m : Nat} (d : Dag Γ m) : List Nat :=
  List.ofFn (fun i => encodePort (d.ports i))

def stateOf {Γ : List Ty} {m : Nat} (d : Dag Γ m) (pending : List Lowering) : InputState :=
  (Γ.map SyntaxCode.typeCode,encodeRows d.wires,encodedPorts d,pending)

theorem rows_state_length {Γ : List Ty} {m : Nat} (d : Dag Γ m) (pending : List Lowering) :
    (stateOf d pending).2.1.length = m :=
  BooleanMatrix.encode_rows_length d.wires

private theorem encode_map_wires {n k m : Nat} (r : Fin n → Fin k) (hr : ∀ j, (r j).val = j.val)
    (d : BooleanWire.Dag n m) :
    encodeRows (InputNormalization.mapDag r d) = encodeRows d := by
  induction d with
  | nil => rfl
  | snoc d row ih => cases row <;> simp [InputNormalization.mapDag, InputNormalization.mapNode,
      encodeRows, encodeRow, hr, ih]

private theorem encoded_ports_snoc {Γ : List Ty} {m : Nat} (d : Dag Γ m) (row : InputNormalization.Node Γ m) :
    encodedPorts (.snoc d row) = encodedPorts d ++ [encodePort (row.ports 0), encodePort (row.ports 1)] := by
  unfold encodedPorts
  change List.ofFn (fun i : Fin (arity m + 2) => encodePort (Fin.addCases d.ports row.ports i)) = _
  rw [List.ofFn_add]
  congr 1
  · apply congrArg List.ofFn
    funext i
    rw [show i.castLE (Nat.le_add_right (arity m) 2) = Fin.castAdd 2 i from rfl, Fin.addCases_left]
  · simp only [Fin.addCases_right, List.ofFn_succ, List.ofFn_zero]
    rfl

theorem add_row_state {Γ : List Ty} {m : Nat} (d : Dag Γ m) (row : InputNormalization.Node Γ m) (pending : List Lowering) :
    addRow (stateOf d pending) (encodeInputRow row) = stateOf (.snoc d row) pending := by
  have hr : encodeRows (Dag.snoc d row).wires = encodeRow row.wire :: encodeRows d.wires := by
    simp only [Dag.wires, encodeRows, encode_map_wires (Fin.castAdd 2) (fun _ => rfl)]
  simp only [stateOf, hr, encoded_ports_snoc]
  cases row <;> simp [addRow, encodeInputRow, InputNormalization.Node.wire, InputNormalization.Node.ports, encodeRow,
    encodedPorts, encodePort]

private theorem renamed_wire {Γ Θ : List Ty} {m : Nat} (d : Dag Γ m) (r : Renaming Γ Θ) :
    (d.rename r).wires = d.wires := by
  induction d with
  | nil => rfl
  | snoc d row ih => cases row <;> simp [Dag.rename, Dag.wires, InputNormalization.Node.rename, InputNormalization.Node.wire, ih]

private theorem node_ports_rename {Γ Θ : List Ty} {m : Nat} (row : InputNormalization.Node Γ m)
    (r : Renaming Γ Θ) (j : Fin 2) :
    (row.rename r).ports j = ExistentialPlan.portRename r (row.ports j) := by
  cases row <;> exact Fin.cases rfl (fun _ => rfl) j

private theorem ports_rename {Γ Θ : List Ty} {m : Nat} (d : Dag Γ m) (r : Renaming Γ Θ)
    (j : Fin (arity m)) :
    (d.rename r).ports j = ExistentialPlan.portRename r (d.ports j) := by
  induction d with
  | nil => exact Fin.elim0 j
  | @snoc k d row ih =>
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa [Dag.rename, Dag.ports] using ih i
      · simpa [Dag.rename, Dag.ports] using node_ports_rename row r i

theorem add_wire_state {Γ : List Ty} {m : Nat} (d : Dag Γ m) (pending : List Lowering)
    (op : Lowering) :
    addWire (stateOf d pending) op =
      stateOf (d.rename (Renaming.weaken Γ .ground)) (op :: pending) := by
  have hports : (encodedPorts d).map (shiftPort 1) =
      encodedPorts (d.rename (Renaming.weaken Γ .ground)) := by
    simp only [encodedPorts, List.map_ofFn, ports_rename]
    apply congrArg List.ofFn
    funext i
    exact shift_port_code 1 (d.ports i)
  simp only [addWire, stateOf, renamed_wire, hports]
  rfl

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler
