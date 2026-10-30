module
public import LogicLineages.OrdinalComparison.CartierRationalDefinitions
public import Mathlib.FieldTheory.RatFunc.Degree

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison

/-- Literal properness of the canonical rational fraction, using WithBot
polynomial degree so the zero rational function is properly included. -/
def actualRationalProper {K : Type u} [Field K] (f : RatFunc K) : Prop :=
  f.num.degree < f.denom.degree

end LogicLineages.OrdinalComparison
