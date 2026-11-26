module
public import LogicLineages.PermittedControl.OriginalPrintedRawTerminalRowsTargets
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeCalibrationProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawTerminalRows
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open HeterogeneousSignedMatrixSlice (encodeRow encodeTest)
open MixedSameRankResidue (encodeWeighted)
open PreparedProjection (LowerOperand)
open OriginalPlainTerminalMatrix (atomRow atomTest rows)

private theorem weightedLiteral (t : Int × NormalForm.Summand) :
    weightedCode (t.1,t.2.data) = encodeWeighted (t.1,.coordinate t.2.name) := by
  rcases t with ⟨c,s⟩
  cases s <;> rfl

private theorem weightsLiteral (rs : List (Int × NormalForm.Summand)) :
    (rs.map (fun t => (t.1,t.2.data))).map weightedCode =
      (rs.map (fun t => (t.1,LowerOperand.coordinate t.2.name))).map encodeWeighted := by
  simp only [List.map_map,Function.comp_def]
  exact List.map_congr_left (fun t _ => weightedLiteral t)

theorem exactOriginalRawTerminalAtoms : ExactOriginalRawTerminalAtoms := by
  intro a
  simp only [LinearRows.Code.decodeAtom,Encodable.encodek,Option.getD_some]
  cases a <;> simp [atomCode,NormalForm.Atom.data,NormalForm.rowData,atomRow,
    atomTest,NormalForm.Atom.row,encodeRow,encodeTest,testCode,List.map_map,Function.comp_def,weightedLiteral]

theorem exactOriginalRawTerminalRows : ExactOriginalRawTerminalRows := by
  intro p
  have lit : rowsCode p.encode = (rows p).map encodeRow := by
    simp only [rowsCode,LinearRowsCodeProof.atoms_calibration,rows,List.map_map,Function.comp_def]
    exact List.map_congr_left (fun a _ => exactOriginalRawTerminalAtoms a)
  exact ⟨lit,by rw [lit]; simp [rows]⟩

end LogicLineages.PermittedControl.OriginalPrintedRawTerminalRows
