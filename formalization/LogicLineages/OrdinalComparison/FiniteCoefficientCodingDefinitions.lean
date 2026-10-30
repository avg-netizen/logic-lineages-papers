module
public import Mathlib.Data.Nat.Digits.Lemmas

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Literal weighted slope, with coordinate zero carrying weight one. -/
def finiteCoefficientSlope (B : Nat) (xs : List Nat) : Nat :=
  xs.foldr (fun a s => a+B*s) 0

/-- Actual finite raw-coefficient maximum; the empty family has base two. -/
def finiteCoefficientBase (rows : List (List Nat)) : Nat :=
  max 2 (rows.flatten.foldr max 0 + 1)

end LogicLineages.OrdinalComparison
