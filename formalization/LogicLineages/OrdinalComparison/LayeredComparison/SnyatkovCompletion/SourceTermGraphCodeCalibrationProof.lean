module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof
open CommonLayerSyntax SourceTermGraph

private theorem instructions_step (n tag : Nat) (ht : tag < 4) :
    Code.instructions (4 * n + tag) =
      if tag = 0 then [(0, n)]
      else if tag = 1 then [(1, n)]
      else if tag = 2 then
        Code.instructions n.unpair.1 ++ Code.instructions n.unpair.2 ++ [(2, 0)]
      else Code.instructions n ++ [(3, 0)] := by
  have hm : (4 * n + tag) % 4 = tag := by omega
  have hd : (4 * n + tag) / 4 = n := by omega
  rw [Code.instructions, hm, hd]

theorem instructions_calibration (t : BaseTerm) :
    Code.instructions t.encode = instructions t := by
  induction t with
  | numeral n =>
      simpa [BaseTerm.encode, instructions] using instructions_step n 0 (by decide)
  | «variable» i =>
      simpa [BaseTerm.encode, instructions] using instructions_step i 1 (by decide)
  | add a b ha hb =>
      simpa [BaseTerm.encode, instructions, Nat.unpair_pair, ha, hb] using
        instructions_step (Nat.pair a.encode b.encode) 2 (by decide)
  | phi a ha =>
      simpa [BaseTerm.encode, instructions, ha] using
        instructions_step a.encode 3 (by decide)

theorem instructions_length (t : BaseTerm) :
    (instructions t).length = nodeCount t := by
  induction t with
  | numeral n => rfl
  | «variable» i => rfl
  | add a b ha hb => simp [instructions, nodeCount, ha, hb, Nat.add_assoc]
  | phi a ha => simp [instructions, nodeCount, ha]

theorem instructionCodeCalibration : SourceTermGraphTargets.InstructionCodeCalibration :=
  fun t => ⟨instructions_calibration t, instructions_length t⟩

theorem numeralRow_data (z n : Nat) :
    NormalForm.rowData (numeralRow z n) = Code.numeralRow z n := rfl
theorem variableRow_data (z i : Nat) :
    NormalForm.rowData (variableRow z i) = Code.variableRow z i := rfl
theorem additionRow_data (z x y : Nat) :
    NormalForm.rowData (additionRow z x y) = Code.additionRow z x y := rfl
theorem phiRow_data (z x : Nat) :
    NormalForm.rowData (phiRow z x) = Code.phiRow z x := rfl

private theorem output_add (start : Nat) (a b : BaseTerm) :
    output start (.add a b) = start + nodeCount a + nodeCount b := by
  simp only [output, nodeCount]
  omega
private theorem output_phi (start : Nat) (a : BaseTerm) :
    output start (.phi a) = start + nodeCount a := by
  simp only [output, nodeCount]
  omega

theorem run_append (left right : List Instruction) (s : Code.State) :
    Code.run (left ++ right) s = Code.run right (Code.run left s) :=
  List.foldl_append

private theorem run_numeral (start n : Nat) (stack : List Nat)
    (prior : List Code.RowData) :
    Code.run [(0, n)] (start, stack, prior) =
      (start + 1, start :: stack, prior ++ [Code.numeralRow start n]) := rfl
private theorem run_variable (start i : Nat) (stack : List Nat)
    (prior : List Code.RowData) :
    Code.run [(1, i)] (start, stack, prior) =
      (start + 1, start :: stack, prior ++ [Code.variableRow start i]) := rfl
private theorem run_addition (start x y : Nat) (stack : List Nat)
    (prior : List Code.RowData) :
    Code.run [(2, 0)] (start, y :: x :: stack, prior) =
      (start + 1, start :: stack, prior ++ [Code.additionRow start x y]) := rfl
private theorem run_phi (start x : Nat) (stack : List Nat)
    (prior : List Code.RowData) :
    Code.run [(3, 0)] (start, x :: stack, prior) =
      (start + 1, start :: stack, prior ++ [Code.phiRow start x]) := rfl

/-- The postfix machine appends exactly the typed postorder rows and preserves
every entry below the new term result, for arbitrary initial machine data. -/
theorem rowMachineCalibration : SourceTermGraphTargets.RowMachineCalibration := by
  intro t
  induction t with
  | numeral n =>
      intro start stack prior
      rw [instructions, run_numeral]
      simp [nodeCount, output, rows, numeralRow_data]
  | «variable» i =>
      intro start stack prior
      rw [instructions, run_variable]
      simp [nodeCount, output, rows, variableRow_data]
  | add a b ha hb =>
      intro start stack prior
      rw [instructions, run_append, run_append, ha, hb, run_addition]
      simp [nodeCount, rows, output_add, additionRow_data,
        Nat.add_assoc, List.append_assoc]
  | phi a ha =>
      intro start stack prior
      rw [instructions, run_append, ha, run_phi]
      simp [nodeCount, rows, output_phi, phiRow_data,
        Nat.add_assoc, List.append_assoc]

theorem negateRow_data (row : NormalForm.Row) :
    NormalForm.rowData (negateRow row) = Code.negateRow (NormalForm.rowData row) := by
  simp [negateRow, Code.negateRow, NormalForm.rowData, List.map_map]

theorem equation_calibration (row : NormalForm.Row) :
    Code.equation (NormalForm.rowData row) = (equation row).encode := by
  simp only [Code.equation, Code.conjunction, Code.atom, equation,
    NormalForm.Formula.encode, NormalForm.Atom.data, negateRow_data]

theorem equations_calibration (rs : List NormalForm.Row) :
    Code.equations (rs.map NormalForm.rowData) = (equations rs).encode := by
  induction rs with
  | nil => rfl
  | cons row rs ih =>
      change Code.conjunction (Code.equation (NormalForm.rowData row))
        (Code.equations (rs.map NormalForm.rowData)) =
          6 * Nat.pair (equation row).encode (equations rs).encode + 4
      rw [equation_calibration, ih]
      rfl

theorem literalGraphCompiler : SourceTermGraphTargets.LiteralGraphCompiler := by
  intro t start
  simp only [Code.package, instructions_calibration]
  rw [rowMachineCalibration t start [] []]
  simp only [List.nil_append, equations_calibration, output, graph]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof
