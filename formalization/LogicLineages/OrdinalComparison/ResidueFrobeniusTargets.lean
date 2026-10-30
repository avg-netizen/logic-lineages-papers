module
public import LogicLineages.OrdinalComparison.LinkedResidueLaurentTargets

@[expose] public section

/-! Actual residue suppliers for paper10 thm:actual-period. Both statements
use the coefficient of the genuine shifted Laurent expansion, literal Phi
parameters, and arbitrary characteristic-two field extensions. They certify
an upper period and exclude its midpoint, not yet exact tuple period or any
Cartier-orbit period. No finite-field-membership hypothesis is assumed. -/

universe u
namespace LogicLineages.OrdinalComparison.Targets

def ActualResidueFrobeniusUpperPeriod : Prop :=
  ∀ (K : Type u) [Field K] [Algebra (ZMod 2) K], ∀ u : Nat, 5 ≤ u →
    ∀ z : K, IsPrimitiveRoot z (actualLinkedModulus u) →
      ((actualLinkedResidueExpansion u z).coeff (-1)) ^
        (2 ^ (2 * actualLinkedHalfExponent u)) =
      (actualLinkedResidueExpansion u z).coeff (-1)

def ActualResidueFrobeniusMidpointNonfixed : Prop :=
  ∀ (K : Type u) [Field K] [Algebra (ZMod 2) K], ∀ u : Nat, 5 ≤ u →
    ∀ z : K, IsPrimitiveRoot z (actualLinkedModulus u) →
      ((actualLinkedResidueExpansion u z).coeff (-1)) ^
        (2 ^ actualLinkedHalfExponent u) ≠
      (actualLinkedResidueExpansion u z).coeff (-1)

end LogicLineages.OrdinalComparison.Targets
