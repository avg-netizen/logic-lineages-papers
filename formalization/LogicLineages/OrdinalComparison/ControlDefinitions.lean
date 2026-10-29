module
public import Mathlib.Logic.Function.Iterate

@[expose] public section

/-!
# The literal numerical control, independent of ordinal notation imports

The source definitions are separated so elementary control lemmas do not
need to load the complete ordinal-calculator development.
-/

namespace LogicLineages.OrdinalComparison

/-- `F₀(n)=2^n`, `Fⱼ₊₁(n)=Fⱼ^[n+1](n)`. -/
def fastControl : Nat → Nat → Nat
  | 0, n => 2 ^ n
  | j + 1, n => (fastControl j)^[n + 1] n

/-- The exact fixed control occurring in papers 05--10. -/
def Phi (n : Nat) : Nat := fastControl 5 (n + 100)

end LogicLineages.OrdinalComparison
