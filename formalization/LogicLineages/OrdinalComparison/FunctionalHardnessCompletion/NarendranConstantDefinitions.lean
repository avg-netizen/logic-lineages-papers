module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.NarendranDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.Narendran
open Polynomial

/-- Nonnegative quotient of X^n-2^n by X-2, built without subtraction. -/
noncomputable def atTwoPower : Nat → NPolynomial
  | 0 => 0
  | n+1 => X*atTwoPower n+C (2^n)
noncomputable def atTwoQuotient (p : NPolynomial) : NPolynomial :=
  p.sum fun n c => C c*atTwoPower n

/-- Nonnegative quotient of p(X^2)-p(X) by X-1. -/
noncomputable def doubleDifference (p : NPolynomial) : NPolynomial :=
  p.sum fun n c => C c*X^n*geometric n

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.Narendran
