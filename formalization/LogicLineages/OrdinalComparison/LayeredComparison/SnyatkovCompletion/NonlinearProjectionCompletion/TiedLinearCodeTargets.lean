module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeTargets
open TiedLinearCode

/-- Literal token order, duplicates and roles, not merely token-set equality. -/
def LiteralTokenCalibration : Prop := ∀ p : BlockRows.Formula,
  tokens (BlockFormulaSubstitutionCode.formulaCode p) = (TiedLinear.tokens p).map tokenData

def LiteralLiftCalibration : Prop :=
  ∀ (table : List TiedLinear.Token) (x : Nat) (p : BlockRows.Formula),
    liftFormula (table.map tokenData) x (BlockFormulaSubstitutionCode.formulaCode p) =
      (TiedLinear.liftFormula table x p).encode

/-- Includes the original parameter-zero fallback for nonlinear summands;
no claim that the input was produced by Cooper is required. -/
def LiteralLowerCalibration : Prop :=
  ∀ (table : List TiedLinear.Token) (x : Nat) (p : NormalForm.Formula),
    lowerFormula (table.map tokenData) x p.encode =
      BlockFormulaSubstitutionCode.formulaCode (TiedLinear.lowerFormula table x p)

/-- Exact code equality to the unchanged full original tied adapter.
No linearity or supplied-effectivity premise is added to this calibration. -/
def LiteralEliminationCalibration : Prop := ∀ (x : Nat) (p : BlockRows.Formula),
  eliminate x (BlockFormulaSubstitutionCode.formulaCode p) =
    BlockFormulaSubstitutionCode.formulaCode (TiedLinear.eliminate x p)

/-- Actual all-code adapters with tables, names and syntax as runtime data. -/
def ActualAdapterPrograms : Prop :=
  Computable tokens ∧
  Computable (fun p : AdapterInput => liftFormula p.1 p.2.1 p.2.2) ∧
  Computable (fun p : AdapterInput => lowerFormula p.1 p.2.1 p.2.2)

/-- One closed actual program, jointly in the original selected name and code. -/
def ActualEliminationProgram : Prop := Computable₂ eliminate

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeTargets
