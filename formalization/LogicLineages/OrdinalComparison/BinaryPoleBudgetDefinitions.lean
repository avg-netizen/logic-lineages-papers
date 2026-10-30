module
public import LogicLineages.OrdinalComparison.BinaryDenominatorDefinitions
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Literal source μ: the sum of the characteristic-two multiplicity factors,
not a degree surrogate or an assumed pole bound. -/
noncomputable def actualBinaryPoleBudget (d : Nat) : Nat :=
  ∑ i : Fin d, 2 ^ padicValNat 2 (i.val + 1)

end LogicLineages.OrdinalComparison
