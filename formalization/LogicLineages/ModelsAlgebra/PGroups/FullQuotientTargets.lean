module

public import LogicLineages.ModelsAlgebra.PGroups.QuotientUlmDefinitions
public import Mathlib.LinearAlgebra.Dimension.Basic

@[expose] public section

/-!
The full two-conclusion statement of paper 01's
`lem:quotient-filtration`. Actual ordinal-recursive stages, the actual
quotient projection, p-socle quotients, constructed scalar actions, and
the specific induced linear map occur in the type. No isomorphism,
linearity, rank, or ordinal-cut supplier is an input.

The theorem is generalized from countable abelian p-groups to all
abelian groups; the source's prime-p and ordinal-product conventions
are retained. The separate first-conclusion gate is already accepted.
-/

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

universe u v

def fullQuotientFiltrationLemma : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) [Fact p.Prime]
    (T : AddSubgroup G) (γ : Ordinal.{v})
    (hT : T ≤ transfiniteFiltration p (Ordinal.omega0 * γ)),
    (∀ α ≤ Ordinal.omega0 * γ,
      (transfiniteFiltration p α : AddSubgroup (G ⧸ T)) =
        (transfiniteFiltration p α : AddSubgroup G).map (QuotientAddGroup.mk' T)) ∧
    ∀ β (hβ : β < Ordinal.omega0 * γ),
      Function.Bijective (quotientUlmMap p T (Ordinal.omega0 * γ) hT β hβ.le) ∧
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p β : AddSubgroup G)) =
        Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p β : AddSubgroup (G ⧸ T)))

end LogicLineages.ModelsAlgebra.PGroups.Targets
