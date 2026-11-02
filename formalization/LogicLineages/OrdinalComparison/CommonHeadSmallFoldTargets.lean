module
public import LogicLineages.OrdinalComparison.CommonHeadSmallFoldDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.CommonHeadSmallFold.Targets
open CommonHeadLargeRow

/-- The real closed evaluator, not a head oracle. Calibration includes the
truncated subtraction outside the genuine domain; source folds are genuine. -/
def ClosedEvaluation : Prop := Computable₂ closedValueCode ∧
  ∀ rho : NONote, ∀ c : Nat,
    closedValueCode (rawNoteEncode rho.1) c=actualHeadValue rho.1.repr c ∧
    ∀ K row, smallValuesCode (rawNoteEncode rho.1) K row=smallValues rho.1.repr K row

/-- A single occurrence is removed, not its entire equal-input block. -/
def ExactOccurrenceFold : Prop := ∀ (lam : Ordinal) (K : Int) (row : Row)
  (i : Fin row.length) (c : Nat), row[i].2=c →
  value lam (foldedConstant lam K row i c) (remaining row i)=value lam K row ∧
  (remaining row i).length+1=row.length ∧
  ((∀ a∈row, actualOrdinalNorm lam≤a.2) →
    ∀ a∈remaining row i, actualOrdinalNorm lam≤a.2)

/-- Exhaustive finite guards at the current row's threshold. Subsequent calls
must recompute the threshold from the updated constant and shorter row. -/
def ExhaustiveSmallBranch : Prop := ∀ (lam : Ordinal) (K : Int) (row : Row),
  (∀ a∈row, actualOrdinalNorm lam≤a.2) →
  (∀ a∈row, threshold K row≤a.2) ∨
  ∃ (i : Fin row.length) (c : Nat), c∈smallValues lam K row ∧ row[i].2=c ∧
    value lam (foldedConstant lam K row i c) (remaining row i)=value lam K row ∧
    (remaining row i).length<row.length
end LogicLineages.OrdinalComparison.CommonHeadSmallFold.Targets
