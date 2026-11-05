module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitNumericTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitNumeric.Proof
open LogicLineages.ComputabilityKnowledge.CircuitReduction
open CircuitLinear

private theorem gateCodeRows_cons (n g start tag x y : Nat) (code : List Nat) :
    gateCodeRows n g start (tag :: x :: y :: code) =
      gateRecordRows n g start tag x y ++ gateCodeRows n g (start+1) code := by
  have hlen : (tag :: x :: y :: code).length / 3 = code.length / 3 + 1 := by
    simp only [List.length_cons]
    omega
  simp only [gateCodeRows, hlen, List.range_succ_eq_map, List.flatMap_cons,
    List.flatMap_map, Nat.mul_zero, Nat.add_zero,
    List.getD_cons_zero, List.getD_cons_succ]
  congr 1
  apply congrArg (fun f : Nat → List Row => (List.range (code.length / 3)).flatMap f)
  funext j
  simp only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one, Nat.add_assoc,
    List.getD_cons_succ]
  congr 1
  omega

theorem gateCodeCalibration : Targets.GateCodeCalibration := by
  intro n g start gs
  induction gs generalizing start with
  | nil => simp [gateCodeRows, encodeGates]
  | cons gate gs ih =>
    cases gate <;>
      simp [encodeGates, encodeGate, gateCodeRows_cons, ih, gateRecordRows]

private theorem encodedGates_length (gs : List Gate) :
    (encodeGates gs).length = 3 * gs.length := by
  induction gs with
  | nil => rfl
  | cons gate gs ih =>
    cases gate <;> simp [encodeGates, encodeGate, ih, Nat.mul_add] <;> omega

theorem systemCodeCalibration : Targets.SystemCodeCalibration := by
  intro c
  have hg : (encodeGates c.gates).length / 3 = c.gates.length := by
    rw [encodedGates_length]
    omega
  simp [systemFromCode, encodeCircuit, encodeCircuitSystem, hg]
  exact gateCodeCalibration c.inputCount c.gates.length 0 c.gates

theorem encoderCalibration : Targets.EncoderCalibration := by
  intro c
  exact congrArg (fun s : SystemCode => some (Encodable.encode s)) (systemCodeCalibration c)

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitNumeric.Proof
