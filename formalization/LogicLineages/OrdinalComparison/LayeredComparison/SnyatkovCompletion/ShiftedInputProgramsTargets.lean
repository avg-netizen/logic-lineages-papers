module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputProgramsDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputProgramsTargets
open NormalForm ShiftedInputGuards ShiftedInputPrograms

def LiteralAtomicCodes : Prop :=
  (∀ a b : Input, Code.less a b = (ShiftedInputGuards.less a b).encode) ∧
  (∀ a b : Input, Code.equal a b = (ShiftedInputGuards.equal a b).encode) ∧
  (∀ (c : Nat) (a : Input), Code.bound c a = (ShiftedInputGuards.bound c a).encode)

def LiteralPostfixCompiler : Prop := ∀ (xs : List Input) (p : CommonHeadLargeGuards.Formula),
  Code.compile xs (CommonHeadCompiler.encode p) = (ShiftedInputGuards.compile xs p).encode

def LiteralOriginalData : Prop := ∀ r : Row,
  Code.occurrences (rowData r) = ShiftedInputGuards.occurrences r ∧
    Code.coefficients (rowData r) = ShiftedInputGuards.coefficients r ∧
    Code.inputs (rowData r) = ShiftedInputGuards.inputs r

def LiteralGuardPrograms : Prop :=
  (∀ r : Row, Code.canceled (rowData r) = (ShiftedInputGuards.canceled r).encode) ∧
  (∀ (r : Row) (k : Nat) (desired : Int),
    Code.block (rowData r) k desired = (ShiftedInputGuards.block r k desired).encode) ∧
  (∀ (r : Row) (desired : Int),
    Code.activeSign (rowData r) desired = (ShiftedInputGuards.activeSign r desired).encode)

def ActualCompilerPrograms : Prop :=
  Primrec₂ Code.less ∧ Primrec₂ Code.equal ∧ Primrec₂ Code.bound ∧ Primrec₂ Code.compile

def ActualSourceGuardPrograms : Prop :=
  Primrec Code.occurrences ∧ Primrec Code.coefficients ∧ Primrec Code.inputs ∧
    Primrec Code.canceled ∧
    Primrec (fun p : NormalForm.Code.RowData × Nat × Int => Code.block p.1 p.2.1 p.2.2) ∧
    Primrec₂ Code.activeSign

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputProgramsTargets
