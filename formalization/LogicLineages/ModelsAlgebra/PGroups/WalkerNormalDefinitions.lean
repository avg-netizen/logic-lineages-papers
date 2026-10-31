module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerPresentedDefinitions
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

/-- Literal finite natural-coefficient sum in the indicated additive group. -/
def walkerDigitSum {V G : Type} [AddCommGroup G] (gen : V → G) (d : V →₀ ℕ) : G :=
  d.sum (fun v c => c • gen v)

/-- Ordinary unique base-p finite expression, not a field of a structure. -/
def WalkerDigitNormalForm {V G : Type} [AddCommGroup G] (p : ℕ) (gen : V → G) : Prop :=
  ∀ x : G, ∃! d : V →₀ ℕ, (∀ v, d v < p) ∧ walkerDigitSum gen d = x

end LogicLineages.ModelsAlgebra.PGroups
