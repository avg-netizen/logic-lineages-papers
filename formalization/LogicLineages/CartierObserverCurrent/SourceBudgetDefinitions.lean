module
public import LogicLineages.CartierObserverCurrent.MixedProperDefinitions
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Nat.Log

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.SourceBudget

/-- Every literal source factor, indexed by integers 1 through d. -/
noncomputable def denominator (K : Type u) [Field K] (d : Nat) : Polynomial K :=
  ∏ i : Fin d, (1 + Polynomial.X ^ (i.val + 1))

/-- Source mu: sum of actual two-adic multiplicity factors, not degree. -/
noncomputable def budget (d : Nat) : Nat :=
  ∑ i : Fin d, 2 ^ padicValNat 2 (i.val + 1)

/-- Used with d>=1, so mu>0 and this is the ordinary ceiling-log transient. -/
noncomputable def transient (d : Nat) : Nat := Nat.clog 2 (budget d)
end LogicLineages.CartierObserverCurrent.SourceBudget
