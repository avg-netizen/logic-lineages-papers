module
public import LogicLineages.OrdinalComparison.ProfileCompilerDefinitions
public import LogicLineages.OrdinalComparison.EncodedCollapseDefinitions
public import LogicLineages.OrdinalComparison.FiniteTail

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Exact structural occurrence detector on the already accepted literal P1
source tree. No additional input constructor is introduced. -/
def positiveExprHasInput : FixedLimitPositiveExpr → Bool
  | .constant _ => false
  | .input => true
  | .add E F => positiveExprHasInput E || positiveExprHasInput F
  | .head _ E => positiveExprHasInput E

/-- Concrete closed-fold partial program, with input interpreted as zero.
On input-free source trees its value is independent of that convention.
Every head invokes the actual accepted raw-code collapse program. -/
def positiveClosedProgram : FixedLimitPositiveExpr → Part Nat
  | .constant n => Part.some n
  | .input => Part.some 0
  | .add E F => (positiveClosedProgram E).bind fun a =>
      (positiveClosedProgram F).map fun b => a+b
  | .head rho E => (positiveClosedProgram E).bind fun n =>
      encodedCollapsePartial (rawNoteEncode (finiteTail rho n).1)

end LogicLineages.OrdinalComparison
