module
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Finite
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

/-- A literal finite cyclic-length list realizing given finite multiplicities. -/
def groupFiniteMultiplicityEnumeration : Prop :=
  ∀ (n : ℕ) (m : Fin n → ℕ), ∃ (t : ℕ) (ell : Fin t → ℕ),
    (∀ a : Fin t, 1 ≤ ell a ∧ ell a ≤ n) ∧
    (∀ j : Fin n, Nat.card {a : Fin t // ell a = j.val+1} = m j)

end LogicLineages.ModelsAlgebra.PGroups.Targets
