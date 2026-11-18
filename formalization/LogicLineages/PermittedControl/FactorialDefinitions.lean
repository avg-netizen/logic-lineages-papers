module
public import LogicLineages.PermittedControl.Definitions
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section
namespace LogicLineages.PermittedControl

/-- Paper17 eq:factorial-control. Exactness of the subtraction as an integer
expression, including n=0 and n=1, is a separate frozen obligation. -/
def factorialControl (n : Nat) : Nat := Nat.factorial (G n) + 2 * potential n - 2

end LogicLineages.PermittedControl
