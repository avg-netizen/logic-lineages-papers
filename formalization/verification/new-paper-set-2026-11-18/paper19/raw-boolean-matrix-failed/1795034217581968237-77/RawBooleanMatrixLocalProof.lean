module
public import LogicLineages.ControlSensitivityCurrent.RawBooleanMatrixTargets
public import LogicLineages.ControlSensitivityCurrent.RawPrimitiveGateVertexProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.BooleanMatrix

open LogicLineages.OrdinalComparison.Source PrimitiveLowering
open PrimitiveGate (encodePort encodeGate fresh_index variable_shift_index)
open BinaryPlanCompiler (shiftPort)

theorem input_port_code {Γ : List Ty} (m : Nat) (p : Port Γ) :
    encodePort (BooleanFlatten.inputPort m p) = shiftPort (oneCode m) (encodePort p) := by
  cases p with
  | zero => rfl
  | var x =>
      simp only [BooleanFlatten.inputPort, encodePort, shiftPort, oneCode, Nat.add_one_ne_zero,
        if_false, variable_shift_index]
      omega

theorem bit_port_code {Γ : List Ty} {m : Nat} (i : Fin m) :
    encodePort (BooleanFlatten.bitPort (Γ := Γ) i) = bitCode i.val := by
  simp [BooleanFlatten.bitPort, BooleanFlatten.bitIndex, encodePort, fresh_index, bitCode]

theorem auxiliary_port_code {Γ : List Ty} {m : Nat} (i : Fin m) (j : Fin 8) :
    encodePort (BooleanFlatten.auxPort (Γ := Γ) i j) = auxiliaryCode i.val j.val := by
  simp [BooleanFlatten.auxPort, BooleanFlatten.auxIndex, encodePort, fresh_index, auxiliaryCode]
  omega

theorem one_port_code (Γ : List Ty) (m : Nat) :
    encodePort (BooleanFlatten.onePort (Γ := Γ) m) = oneCode m := by
  simp [BooleanFlatten.onePort, BooleanFlatten.oneIndex, encodePort, fresh_index, oneCode]

theorem input_lookup {Γ : List Ty} {n : Nat} (a : Fin n → Port Γ) (j : Fin n) :
    (List.ofFn (fun i => encodePort (a i))).getD j.val 0 = encodePort (a j) := by
  simp [List.getD_eq_getElem?_getD, j.isLt]

theorem local_exactness {Θ : List Ty} {n k : Nat} (m i : Nat) (ports : List Nat)
    (row : BooleanWire.Node n k) (a : Fin n → Port Θ) (w : Fin k → Port Θ)
    (out : Port Θ) (z : Fin 8 → Port Θ) (one : Port Θ)
    (ha : ∀ j, encodePort (a j) = shiftPort (oneCode m) (ports.getD j.val 0))
    (hw : ∀ j, encodePort (w j) = bitCode (i+j.val+1))
    (hout : encodePort out = bitCode i)
    (hz : ∀ j, encodePort (z j) = auxiliaryCode i j.val)
    (hone : encodePort one = oneCode m) :
    localRaw m ports i (encodeRow row) =
      (BooleanWire.constraints row).map (fun atom => encodeGate (BooleanFlatten.atomGate a w out z one atom)) := by
  cases row <;>
    simp only [localRaw, encodeRow, BooleanWire.constraints, List.map_cons, List.map_nil,
      BooleanFlatten.atomGate, BooleanFlatten.refPort, encodeGate, eqCode, addCode, sortCode,
      ha, hw, hout, hz, hone]
  all_goals
    first
    | rfl
    | simp only [BooleanWire.zeroAux, List.map_ofFn, BooleanFlatten.atomGate,
        BooleanFlatten.refPort, encodeGate, hz]
      rfl

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.BooleanMatrix
