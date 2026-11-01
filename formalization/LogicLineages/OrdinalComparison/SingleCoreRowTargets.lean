module
public import LogicLineages.OrdinalComparison.SingleCoreRowDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def ActualSingleCoreRowPartsProgram : Prop :=
  Primrec₂ encodedPositiveSourceMultiple ∧ Primrec encodedSingleCoreRowParts ∧
  ∀ row : SingleCoreRow,encodedSingleCoreRowParts (singleCoreRowCode row)=
    (positiveExprEncode (singleCoreRowPart false row),positiveExprEncode (singleCoreRowPart true row))

def ActualSingleCoreRowPartsSemantics : Prop := ∀ row : SingleCoreRow,singleCoreRowValid row →
  fixedLimitProfileBelow epsilonZero (singleCoreRowPart false row) ∧
  fixedLimitProfileBelow epsilonZero (singleCoreRowPart true row) ∧
  ∀ t : Nat,actualSingleCoreRowValue row t=
    (actualFixedLimitProfileEval (singleCoreRowPart false row) t : Int)-
      (actualFixedLimitProfileEval (singleCoreRowPart true row) t : Int)

/-- ENTIRE one-FORMAL-core sign supplier. No claim that the actual multivariate
core ranges freely; the consumer will only substitute its real value. -/
def ActualSingleCoreFormalRowSign : Prop := Computable encodedSingleCoreRowSign ∧
  ∀ row : SingleCoreRow,singleCoreRowValid row →
    let result := encodedSingleCoreRowSign (singleCoreRowCode row)
    result.1≤2 ∧ 1≤result.2 ∧ ∀ t : Nat,result.2≤t →
      (result.1=0 ↔ actualSingleCoreRowValue row t<0) ∧
      (result.1=1 ↔ actualSingleCoreRowValue row t=0) ∧
      (result.1=2 ↔ 0<actualSingleCoreRowValue row t)

def FullActualSingleCoreFormalRow : Prop := ActualSingleCoreRowPartsProgram ∧
  ActualSingleCoreRowPartsSemantics ∧ ActualSingleCoreFormalRowSign

end LogicLineages.OrdinalComparison.Targets
