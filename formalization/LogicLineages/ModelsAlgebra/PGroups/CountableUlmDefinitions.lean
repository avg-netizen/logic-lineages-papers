module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.UlmDefinitions
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.Order.Ideal
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
/-- Actual finite subgroup isomorphism preserving all actual filtration stages.
This is a concrete partial map, not an assumed extension system. -/
structure FiniteHeightIso (p : ℕ) (G H : Type) [AddCommGroup G] [AddCommGroup H] where
  domain : AddSubgroup G
  codomain : AddSubgroup H
  finite_domain : Finite domain
  equiv : domain ≃+ codomain
  preserves : ∀ (x : domain) (α : Ordinal.{0}),
    ((equiv x : H) ∈ transfiniteFiltration p α ↔ (x : G) ∈ transfiniteFiltration p α)
namespace FiniteHeightIso
variable {p : ℕ} {G H : Type} [AddCommGroup G] [AddCommGroup H]
def graph (f : FiniteHeightIso p G H) : Set (G × H) :=
  {z | ∃ hx : z.1 ∈ f.domain, (f.equiv ⟨z.1, hx⟩ : H) = z.2}
instance : Preorder (FiniteHeightIso p G H) := Preorder.lift graph
end FiniteHeightIso
end LogicLineages.ModelsAlgebra.PGroups
