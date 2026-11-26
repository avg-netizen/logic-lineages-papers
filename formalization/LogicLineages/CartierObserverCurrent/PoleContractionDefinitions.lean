module
public import LogicLineages.CartierObserverCurrent.MixedProperDefinitions
public import Mathlib.Algebra.Polynomial.Div

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.PoleContraction

/-- Actual root-removed quotient, not a supplied local regular part. -/
noncomputable def rootRemoved {K : Type u} [Field K] (Q : Polynomial K) (z : K) : Polynomial K :=
  Q.divByMonic ((Polynomial.X - Polynomial.C z) ^ Q.rootMultiplicity z)

/-- Actual order of a finite pole from the reduced canonical denominator. -/
noncomputable def poleOrder {K : Type u} [Field K] (z : K) (f : RatFunc K) : Nat :=
  f.denom.rootMultiplicity z
end LogicLineages.CartierObserverCurrent.PoleContraction
