module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormulaDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedGuardDescentDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedRawCompiler

abbrev Input := BalancedGuardDescent.Input
abbrev Code := BalancedGuardDescent.Code

/-- Literal BASE comparison at the empty actual source shape. Operands are
unchanged BaseTerm codes, not values or labels in an independent valuation.
Every other integer desired sign emits the existing falsity instruction. -/
def baseCode (E F : Nat) (desired : Int) : Code :=
  if desired = 0 then [(2,E,F)]
  else if desired = -1 then [(3,E,F)]
  else if desired = 1 then [(3,F,E)]
  else [(0,0,0)]

/-- Only the actual typed BASE leaf, for literal encoding and sign calibration.
This is not a typed recursive compiler at a positive source shape. -/
def baseFormula (E F : CommonLayerSyntax.BaseTerm) (desired : Int) : BaseFormula.Formula :=
  if desired = 0 then .equal E F
  else if desired = -1 then .less E F
  else if desired = 1 then .less F E
  else .falsity

/-- The raw code constructor recurses on the ACTUAL source shape. Every
lower call uses the child's unchanged certificate, two term codes and sign.
The accepted children all have shape Γ; the exact call target proves that
fact rather than assuming it or replacing the child by a supplied callback.

The output order is frozen: original finite-box code FIRST, recursively
translated original large-guard code SECOND, then literal disjunction. -/
noncomputable def compileCode : List Nat → Nat → Nat → Nat → Int → Code
  | [], _, E, F, desired => baseCode E F desired
  | k :: Γ, C, E, F, desired =>
    CommonHeadCode.disjunction
      (BalancedBoxFormula.formulaCode k Γ C E F desired)
      (BalancedGuardDescent.sourceAssemble k E F desired
        ((BalancedGuardDescent.sourceChildren k Γ C E F desired).map
          (fun a => compileCode Γ a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)))

/-- The precise finite lower-call list, including one ignored Boolean child
per original Boolean instruction. The original lower certificate and all
accepted malformed-input defaults are retained by sourceChildren. -/
noncomputable def children (a : Input) : List Input :=
  match a.1 with
  | [] => []
  | k :: Γ => BalancedGuardDescent.sourceChildren k Γ a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2

/-- Assemble the same two branches in the same literal order. Arbitrary
result lists retain the existing sourceAssemble zip/truncation behavior.
The exact recursion equation supplies precisely one result per child. -/
noncomputable def assemble (a : Input) (results : List Code) : Code :=
  match a.1 with
  | [] => baseCode a.2.2.1 a.2.2.2.1 a.2.2.2.2
  | k :: Γ =>
    CommonHeadCode.disjunction
      (BalancedBoxFormula.formulaCode k Γ a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
      (BalancedGuardDescent.sourceAssemble k a.2.2.1 a.2.2.2.1 a.2.2.2.2 results)

noncomputable def recursiveCode (a : Input) : Code :=
  compileCode a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2

def measure (a : Input) : Nat := a.1.length

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedRawCompiler
