module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationCodeDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationCodeTargets
open WholeBoundInitializationCode

/-- Exact row data for the original initializer, for every bound list and row. -/
def LiteralRowCalibration : Prop := ∀ (bound : List Nat) (r : NormalForm.Row),
  row bound (NormalForm.rowData r) =
    BlockRowSubstitutionCode.rowData (WholeBoundInitialization.row bound r)

def ActualRowProgram : Prop := Computable₂ row

def LiteralAtomCalibration : Prop := ∀ (bound : List Nat) (a : NormalForm.Atom),
  atom bound a.data =
    BlockFormulaSubstitutionCode.atomData (WholeBoundInitialization.atom bound a)

def ActualAtomProgram : Prop := Computable₂ atom

/-- Literal code equality to the unchanged full initializer. No ZeroShift,
Nodup, valuation, validity, or supplied computability premise is needed. -/
def LiteralFormulaCalibration : Prop := ∀ (bound : List Nat) (p : NormalForm.Formula),
  formula bound p.encode =
    BlockFormulaSubstitutionCode.formulaCode (WholeBoundInitialization.«initialize» bound p)

/-- One closed all-code program, jointly in the arbitrary bound list and code. -/
def ActualFormulaProgram : Prop := Computable₂ formula

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationCodeTargets
