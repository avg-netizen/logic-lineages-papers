module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProgramsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainProgramsCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchContextProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProgramsProof
open NormalForm (Formula Atom Summand Row rowData rowVariables)
open MaximalPlainBranchPrograms

private theorem atom_row (a : Atom) : a.data.2.2 = rowData a.row := by cases a <;> rfl
private theorem item_name (s : Summand) : s.data.2.1 = s.name := by cases s <;> rfl
private theorem decode_data (a : Atom) : LinearRows.Code.decodeAtom (Encodable.encode a.data) = a.data := by
  simp only [LinearRows.Code.decodeAtom, Encodable.encodek, Option.getD_some]

theorem isPlain_calibration (p : Formula) : Code.isPlain p.encode = MaximalPlainBranch.isPlain p := by
  simp only [Code.isPlain, MaximalPlainBranch.isPlain, LinearRowsCodeProof.atoms_calibration,
    List.all_map, Function.comp_def, decode_data, atom_row, PlainPhiDominanceProof.isPlain_calibration]

theorem variables_calibration (p : Formula) : Code.variables p.encode = p.variables := by
  rw [MaximalPlainBranchProof.variables_from_atoms p]
  simp only [Code.variables, LinearRowsCodeProof.atoms_calibration, List.flatMap_map,
    Function.comp_def, decode_data, atom_row, rowData, rowVariables, List.map_map, item_name]

theorem cutoff_calibration (p : Formula) : Code.cutoff p.encode = MaximalPlainBranch.cutoff p := by
  simp only [Code.cutoff, MaximalPlainBranch.cutoff, LinearRowsCodeProof.atoms_calibration,
    List.map_map, Function.comp_def, decode_data, MaximalPlainProgramsProof.cutoff_calibration]

theorem literalBranchData : MaximalPlainBranchProgramsTargets.LiteralBranchData :=
  fun p => ⟨isPlain_calibration p, variables_calibration p, cutoff_calibration p⟩

theorem lowerGuard_calibration (i c : Nat) :
    Code.lowerGuard i c = (MaximalPlainBranch.lowerGuard i c).encode := rfl

theorem maximumGuard_calibration (i j : Nat) :
    Code.maximumGuard i j = (MaximalPlainBranch.maximumGuard i j).encode := rfl

private theorem maxima_calibration (i : Nat) (xs : List Nat) :
    xs.foldr (fun j rest => ShiftedInputPrograms.Code.conjunction (Code.maximumGuard i j) rest) 0 =
    (xs.foldr (fun j rest => Formula.conjunction (MaximalPlainBranch.maximumGuard i j) rest) .truth).encode := by
  induction xs with
  | nil => rfl
  | cons j xs ih =>
      simp only [List.foldr_cons]
      rw [ih, maximumGuard_calibration]
      rfl

theorem frame_calibration (i : Nat) (p : Formula) :
    Code.frame i p.encode = (MaximalPlainBranch.frame i p).encode := by
  unfold Code.frame MaximalPlainBranch.frame
  rw [variables_calibration, cutoff_calibration, lowerGuard_calibration, maxima_calibration]
  rfl

theorem literalFrame : MaximalPlainBranchProgramsTargets.LiteralFrame :=
  ⟨lowerGuard_calibration, maximumGuard_calibration, frame_calibration⟩

private theorem compile_step (i payload tag : Nat) (ht : tag < 6) :
    Code.compile i (6 * payload + tag) =
      if tag = 0 then 0 else if tag = 1 then 1
      else if tag = 2 then MaximalPlainPrograms.Code.compileAtom i (LinearRows.Code.decodeAtom payload)
      else if tag = 3 then 6 * Code.compile i payload + 3
      else 6 * Nat.pair (Code.compile i payload.unpair.1)
        (Code.compile i payload.unpair.2) + tag := by
  have hm : (6 * payload + tag) % 6 = tag := by omega
  have hd : (6 * payload + tag) / 6 = payload := by omega
  rw [Code.compile, hm, hd]

theorem compile_calibration (i : Nat) (p : Formula) :
    Code.compile i p.encode = (MaximalPlainBranch.compile i p).encode := by
  induction p with
  | truth => simpa [Formula.encode, MaximalPlainBranch.compile] using compile_step i 0 0 (by decide)
  | falsity => simpa [Formula.encode, MaximalPlainBranch.compile] using compile_step i 0 1 (by decide)
  | atom a =>
      simpa [Formula.encode, MaximalPlainBranch.compile, decode_data,
        MaximalPlainProgramsProof.compileAtom_calibration] using
        compile_step i (Encodable.encode a.data) 2 (by decide)
  | negative p ih =>
      simpa [Formula.encode, MaximalPlainBranch.compile, ih] using compile_step i p.encode 3 (by decide)
  | conjunction p q ihp ihq =>
      simpa [Formula.encode, MaximalPlainBranch.compile, Nat.unpair_pair, ihp, ihq] using
        compile_step i (Nat.pair p.encode q.encode) 4 (by decide)
  | disjunction p q ihp ihq =>
      simpa [Formula.encode, MaximalPlainBranch.compile, Nat.unpair_pair, ihp, ihq] using
        compile_step i (Nat.pair p.encode q.encode) 5 (by decide)

theorem framed_calibration (i : Nat) (p : Formula) :
    Code.framed i p.encode = (MaximalPlainBranch.framed i p).encode := by
  unfold Code.framed MaximalPlainBranch.framed
  rw [frame_calibration, compile_calibration]
  rfl

theorem eliminate_calibration (i : Nat) (p : Formula) :
    Code.eliminate i p.encode = (MaximalPlainBranch.eliminate i p).encode := by
  unfold Code.eliminate MaximalPlainBranch.eliminate
  rw [framed_calibration, LinearRowsCodeProof.eliminate_calibration]

theorem literalBranchCompiler : MaximalPlainBranchProgramsTargets.LiteralBranchCompiler :=
  fun i p => ⟨compile_calibration i p, framed_calibration i p, eliminate_calibration i p⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProgramsProof
