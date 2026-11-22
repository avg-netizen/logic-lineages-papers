module
public import LogicLineages.PermittedControl.InverseTableDefinitions
public import LogicLineages.PermittedControl.PreparedParameterProjectionTargets

@[expose] public section
namespace LogicLineages.PermittedControl.InverseComparisonPreparedRows
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection

/-- Name zero is the greater raw coordinate. Name one receives the
single actual lower-input field value in the inverse table. -/
def greaterMinusParameter (c : Int) : NormalForm.Formula :=
  .atom (.nonnegative (c,[(1,.variable 0),(-1,.variable 1)]))

def parameterMinusGreater (c : Int) : NormalForm.Formula :=
  .atom (.nonnegative (c,[(1,.variable 1),(-1,.variable 0)]))

def equalRows : NormalForm.Formula :=
  .conjunction (greaterMinusParameter 0) (parameterMinusGreater 0)

/-- The requested result is the original comparison of P versus Q.
The printed inverse table states its entries with Q versus P. -/
def emitFormula (sign wanted : Nat) : NormalForm.Formula :=
  if sign = 0 then
    if wanted = 0 then greaterMinusParameter 0
    else if wanted = 2 then parameterMinusGreater (-1)
    else .falsity
  else if sign = 1 then
    if wanted = 0 then greaterMinusParameter (-1)
    else if wanted = 1 then equalRows
    else if wanted = 2 then parameterMinusGreater (-1)
    else .falsity
  else if sign = 2 then
    if wanted = 0 then greaterMinusParameter (-1)
    else if wanted = 2 then parameterMinusGreater 0
    else .falsity
  else .falsity

def emitCode (sign wanted : Nat) : Nat := (emitFormula sign wanted).encode

def CodeExact : Prop :=
  Primrec₂ emitCode ∧
  ∀ sign wanted : Nat, 2 < sign ∨ 2 < wanted →
    emitCode sign wanted = NormalForm.Formula.falsity.encode

def PreparedShape : Prop :=
  ∀ (sign wanted : Nat) (operand : LowerOperand),
    PreparedInput [operand] (emitFormula sign wanted)

/-- The strict raw-coordinate order supplies a positive greater input.
This makes the printed sign-zero row with natural subtraction exact
when expressed by the strict linear comparison, including parameter zero. -/
def ActualInverseRows : Prop :=
  ∀ (sign wanted valueP valueQ : Nat) (ν : Nat → Nat),
    sign ≤ 2 → 0 < ν 0 → InverseTableRows sign (ν 0) (ν 1) valueQ valueP →
    ((emitFormula sign wanted).eval ν ↔ numericalComparison valueP valueQ = wanted)

def FullInverseComparisonPreparedRows : Prop :=
  CodeExact ∧ PreparedShape ∧ ActualInverseRows

end LogicLineages.PermittedControl.InverseComparisonPreparedRows
