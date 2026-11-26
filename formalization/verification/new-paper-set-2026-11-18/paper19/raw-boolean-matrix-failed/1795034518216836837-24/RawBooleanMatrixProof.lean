module
public import LogicLineages.ControlSensitivityCurrent.RawBooleanMatrixLocalProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.BooleanMatrix

open LogicLineages.OrdinalComparison.Source ExistentialPlan PrimitiveLowering
open PlanCompiler (encodePlan)
open BinaryPlanCompiler (binder gate)
open PrimitiveGate (encodePort encodeGate)
open BooleanFlatten (Global inputPort bitPort auxPort onePort flatten)

theorem encode_rows_length {n k : Nat} (d : BooleanWire.Dag n k) : (encodeRows d).length = k := by
  induction d <;> simp_all [encodeRows]

private theorem emit_rows_cons (m : Nat) (ports : List Nat) (offset : Nat) (row : RowCode) (rows : List RowCode) :
    emitRows m ports offset (row :: rows) =
      emitRow m ports (emitRows m ports (offset+1) rows) row := by
  simp only [emitRows, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
    List.length_cons]
  rw [show offset + (rows.length+1) = offset + 1 + rows.length by omega]

private theorem emit_rows_exact {Γ : List Ty} {n k : Nat} (d : BooleanWire.Dag n k)
    (a : Fin n → Port Γ) (m offset : Nat) (bound : offset+k ≤ m) :
    emitRows m (List.ofFn (fun j => encodePort (a j))) offset (encodeRows d) =
      (offset, (flatten d (fun j => inputPort m (a j))
        (fun j => bitPort ⟨offset+j.val, by omega⟩)
        (fun j t => auxPort ⟨offset+j.val, by omega⟩ t) (onePort m)).map encodeGate) := by
  induction d generalizing offset with
  | nil => simp [emitRows, encodeRows, flatten]
  | @snoc k d row ih =>
      simp only [encodeRows, emit_rows_cons]
      rw [ih (offset+1) (by omega)]
      have hlocal := local_exactness m offset (List.ofFn (fun j => encodePort (a j))) row
        (fun j => inputPort m (a j))
        (fun j => bitPort ⟨offset+1+j.val, by omega⟩)
        (bitPort ⟨offset, by omega⟩)
        (fun j => auxPort ⟨offset, by omega⟩ j)
        (onePort m)
        (fun j => by rw [input_port_code, input_lookup])
        (fun j => by rw [bit_port_code]; congr 1; omega)
        (bit_port_code _)
        (fun j => auxiliary_port_code _ j)
        (one_port_code Γ m)
      simp only [emitRow, Nat.add_sub_cancel, hlocal, flatten, List.map_append, List.map_map,
        Function.comp_def, Fin.val_succ]
      have hs (j : Fin k) : offset + 1 + j.val = offset + (j.val + 1) := by omega
      simp only [hs]

private theorem bound_block_code {Γ : List Ty} (n : Nat) (q : Plan (List.replicate n Ty.ground ++ Γ)) :
    encodePlan (BooleanPlan.bindBlock n q) = List.replicate n binder ++ encodePlan q := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BooleanPlan.bindBlock, ih, List.replicate_add]
      simp [encodePlan, binder, List.append_assoc]

private theorem gates_code {Γ : List Ty} (gs : List (Gate Γ)) :
    encodePlan (BooleanPlan.gates gs) = gs.map (fun g => gate (encodeGate g)) := by
  induction gs <;> simp_all [BooleanPlan.gates, encodePlan, gate]

theorem typed_exactness : RawBooleanMatrixTargets.TypedExactness := by
  intro Γ n m d a root
  have hrows := emit_rows_exact d a m 0 (Nat.zero_add m ▸ Nat.le_refl m)
  simp only [matrixRaw, encode_rows_length, BooleanPlan.matrixPlan, bound_block_code, gates_code,
    BooleanFlatten.compile, hrows, List.map_append, List.map_cons, List.map_nil, List.map_map,
    Function.comp_def, one_port_code, bit_port_code, Nat.zero_add, encodeGate, eqCode, oneCode]
  rfl

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.BooleanMatrix
