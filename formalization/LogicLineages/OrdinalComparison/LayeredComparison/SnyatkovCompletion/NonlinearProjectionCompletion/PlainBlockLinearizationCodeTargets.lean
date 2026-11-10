module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCodeDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCodeTargets
open PlainBlockLinearizationCode

/-- Exact occurrence data, signed coefficient sum and original boundary term. -/
def LiteralRowCalibration : Prop := ∀ (i : Nat) (r : BlockRows.Row),
  headCoefficient i (BlockRowSubstitutionCode.rowData r) = PlainMaximum.headCoefficient i r ∧
  remainingOccurrences i (BlockRowSubstitutionCode.rowData r) =
    (PlainMaximum.remainingOccurrences i r).map (fun a => (a.1, a.2.data)) ∧
  mass (BlockRowSubstitutionCode.rowData r) = PlainMaximum.mass r ∧
  boundary i (BlockRowSubstitutionCode.rowData r) = (PlainMaximum.boundary i r).encode

/-- All original guard shapes, including the zero-head case and every band
index. Calibration does not assume domination, allowedness or linearity. -/
def LiteralGuardCalibration : Prop := ∀ (i : Nat) (r : BlockRows.Row),
  positiveGuard i (BlockRowSubstitutionCode.rowData r) =
    BlockFormulaSubstitutionCode.formulaCode (PlainMaximum.positiveGuard i r) ∧
  negativeGuard i (BlockRowSubstitutionCode.rowData r) =
    BlockFormulaSubstitutionCode.formulaCode (PlainMaximum.negativeGuard i r) ∧
  linearizeNonnegative i (BlockRowSubstitutionCode.rowData r) =
    BlockFormulaSubstitutionCode.formulaCode (PlainMaximum.linearizeNonnegative i r) ∧
  outsideRow i (BlockRowSubstitutionCode.rowData r) =
    BlockFormulaSubstitutionCode.formulaCode (PlainBlockSplit.outsideRow i r) ∧
  ∀ d : Nat, bandCandidate i (BlockRowSubstitutionCode.rowData r) d =
    (PlainBlockSplit.bandCandidate i r d).encode

def LiteralResidueCalibration : Prop := ∀ (m i : Nat) (r : BlockRows.Row),
  residueRow m i (BlockRowSubstitutionCode.rowData r) =
    BlockRowSubstitutionCode.rowData (PlainMaximumResidue.lowerRow m i r) ∧
  residueAtom m i (BlockRowSubstitutionCode.rowData r) =
    BlockFormulaSubstitutionCode.formulaCode (PlainMaximumResidue.lowerAtom m i r)

/-- One exact formula compiler, preserving every original Boolean position.
The entire bound list is runtime data, with no Nodup or semantic premise. -/
def LiteralFormulaCalibration : Prop := ∀ (bound : List Nat) (i : Nat) (p : BlockRows.Formula),
  cutoff (BlockFormulaSubstitutionCode.formulaCode p) = PlainBlockSplit.cutoff p ∧
  frame bound i (BlockFormulaSubstitutionCode.formulaCode p) =
    BlockFormulaSubstitutionCode.formulaCode (PlainBlockSplit.frame bound i p) ∧
  outside i (BlockFormulaSubstitutionCode.formulaCode p) =
    BlockFormulaSubstitutionCode.formulaCode (PlainBlockSplit.outside i p) ∧
  linearize i (BlockFormulaSubstitutionCode.formulaCode p) =
    BlockFormulaSubstitutionCode.formulaCode (PlainBlockSplit.linearize i p)

/-- Closed actual row-level programs. No supplied boundary, residue or
recursion effectiveness premise is part of the endpoint. -/
def ActualRowPrograms : Prop :=
  Computable₂ headCoefficient ∧ Computable₂ remainingOccurrences ∧ Computable mass ∧
  Computable₂ boundary ∧ Computable₂ positiveGuard ∧ Computable₂ negativeGuard ∧
  Computable₂ linearizeNonnegative ∧ Computable₂ outsideRow ∧
  Computable (fun p : Nat × (RowData × Nat) => bandCandidate p.1 p.2.1 p.2.2) ∧
  Computable (fun p : Nat × (Nat × RowData) => residueRow p.1 p.2.1 p.2.2) ∧
  Computable (fun p : Nat × (Nat × RowData) => residueAtom p.1 p.2.1 p.2.2)

def ActualFormulaPrograms : Prop :=
  Computable cutoff ∧
  Computable (fun p : List Nat × (Nat × Nat) => frame p.1 p.2.1 p.2.2) ∧
  Computable₂ outside ∧ Computable₂ linearize

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCodeTargets
