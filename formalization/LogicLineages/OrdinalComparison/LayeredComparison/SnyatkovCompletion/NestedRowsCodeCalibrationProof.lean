module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NestedRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SignedRowsCodeCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NestedRowsCodeProof
open NormalForm NestedRows

theorem substitute_calibration (i j : Nat) (a b : Int) (p : Formula) :
    Code.substitute i j a b p.encode = (substitute i j a b p).encode := by
  simp only [Code.substitute, substitute, Formula.encode,
    SignedRows.Code.disjunction, SignedRows.Code.conjunction, SignedRows.Code.negative,
    SignedRowsCodeProof.anchorDomain_calibration, SignedRowsCodeProof.substitute_calibration,
    BoundedRowsCodeProof.formula_calibration]

theorem literalCodeCalibration : NestedRowsTargets.LiteralCodeCalibration :=
  substitute_calibration

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NestedRowsCodeProof
