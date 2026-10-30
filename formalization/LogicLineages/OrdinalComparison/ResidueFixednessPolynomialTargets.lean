module
public import LogicLineages.OrdinalComparison.ResidueFixednessPolynomialDefinitions
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison.Targets

/-! Literal polynomial obstruction in paper10 thm:actual-period, lines620–628.
These are algebraic suppliers, not an assumed count of roots or tuple period. -/
def ActualResidueFixednessPolynomialSize : Prop :=
  ∀ u s : Nat, 5 ≤ u → 0 < s →
    0 < actualLinkedOffset u ∧ actualLinkedOffset u < actualLinkedDegree u ∧
    (actualResidueFixednessPolynomial u s).coeff 0 = 1 ∧
    (actualResidueFixednessPolynomial u s).degree =
      ((2 ^ s * actualLinkedDegree u : Nat) : WithBot Nat)

def ActualResidueFixednessPolynomialRoot : Prop :=
  ∀ (K : Type u) [Field K] [Algebra (ZMod 2) K], ∀ u s : Nat,
    5 ≤ u → 0 < s → ∀ z : K, IsPrimitiveRoot z (actualLinkedModulus u) →
    ((actualLinkedResidueExpansion u z).coeff (-1)) ^ (2 ^ s) =
      (actualLinkedResidueExpansion u z).coeff (-1) →
    Polynomial.eval₂ (algebraMap (ZMod 2) K) z (actualResidueFixednessPolynomial u s) = 0

end LogicLineages.OrdinalComparison.Targets
