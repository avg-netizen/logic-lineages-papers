module
public import LogicLineages.CartierObserverCurrent.SourceBudgetDefinitions
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.SplittingRoots

/-- The actual splitting field of the complete literal source polynomial over F2. -/
noncomputable abbrev FieldAt (d : Nat) := (SourceBudget.denominator (ZMod 2) d).SplittingField

noncomputable def splitPolynomial (d : Nat) : Polynomial (FieldAt d) :=
  (SourceBudget.denominator (ZMod 2) d).map (algebraMap (ZMod 2) (FieldAt d))

/-- All distinct roots of the actual mapped source polynomial, without orbit selection. -/
noncomputable def rootSet (d : Nat) : Finset (FieldAt d) := by
  classical
  exact (splitPolynomial d).roots.toFinset

def Root (d : Nat) := {z : FieldAt d // z ∈ rootSet d}
end LogicLineages.CartierObserverCurrent.SplittingRoots
