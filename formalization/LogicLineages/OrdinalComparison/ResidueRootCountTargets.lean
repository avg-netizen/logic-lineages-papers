module
public import LogicLineages.OrdinalComparison.LinkedResidueLaurentTargets

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison.Targets

/-! Root-count obstruction in paper10 thm:actual-period. An actual primitive
root is an explicit cyclotomic domain condition, not a root-count oracle.
The final source splitting-field application must separately supply it. -/
def ActualResidueSmallExponentNonfixed : Prop :=
  ∀ (K : Type u) [Field K] [Algebra (ZMod 2) K], ∀ u s : Nat,
    5 ≤ u → 0 < s → 3 * s ≤ 2 * actualLinkedHalfExponent u →
    ∀ z₀ : K, IsPrimitiveRoot z₀ (actualLinkedModulus u) →
    ∃ z : K, IsPrimitiveRoot z (actualLinkedModulus u) ∧
      ((actualLinkedResidueExpansion u z).coeff (-1)) ^ (2 ^ s) ≠
        (actualLinkedResidueExpansion u z).coeff (-1)

end LogicLineages.OrdinalComparison.Targets
