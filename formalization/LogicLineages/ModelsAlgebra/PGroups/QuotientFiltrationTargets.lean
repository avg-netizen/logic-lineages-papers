module

public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteDefinitions
public import Mathlib.GroupTheory.QuotientGroup.Defs

@[expose] public section

/-!
The literal quotient-map conclusion of paper 01's
`lem:quotient-filtration`, first displayed equation. The ordinal cut is
generalized from `ωγ` to any cut; the source case is an instance. The
Ulm-quotient isomorphism is a separate unfinished conclusion.
-/

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

universe u v

def quotientFiltrationBelowCut : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (T : AddSubgroup G)
    (δ : Ordinal.{v}), T ≤ transfiniteFiltration p δ →
    ∀ α ≤ δ, (transfiniteFiltration p α : AddSubgroup (G ⧸ T)) =
      (transfiniteFiltration p α : AddSubgroup G).map (QuotientAddGroup.mk' T)

end LogicLineages.ModelsAlgebra.PGroups.Targets
