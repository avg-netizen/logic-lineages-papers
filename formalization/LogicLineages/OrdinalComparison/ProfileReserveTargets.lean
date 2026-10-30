module
public import LogicLineages.OrdinalComparison.ProfileReserveWordTargets
public import LogicLineages.OrdinalComparison.ReserveEndpointTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Full paper07 lem:reserve (464–495) for its literal positive binary-tree
syntax. The executable compiler and threshold are explicit, R/H are calibrated,
and both ordinary and permanent-mass first-finite outcomes are conclusions. -/
def FullActualEffectiveProfileReserve : Prop :=
  ∀ ell : Ordinal.{0}, Ordinal.omega0 < Ordinal.omega0 ^ ell →
    Ordinal.omega0 ^ ell < epsilonZero → ∀ E : FixedLimitPositiveExpr,
    fixedLimitProfileBelow (Ordinal.omega0 ^ ell) E →
    let word := profileBoundWord E
    let R := profileReserveBlocks word
    let H := profileReserveLeadingBound word
    let z0 := fixedLimitProfileThreshold E
    word ≠ [] ∧
    (∀ rho ∈ word, Order.IsSuccLimit rho.1.repr ∧ rho.1.repr < Ordinal.omega0 ^ ell) ∧
    R = (word.map fun rho => actualOrdinalNorm rho.1.repr + 1).sum ∧
    H = (word.map fun rho => actualOrdinalNorm (actualProfileLeadingMonomial rho)).foldr max 0 ∧
    ∀ z : Nat, z0 ≤ z →
      actualFixedLimitProfileEval E z < actualProfileWordValue word z ∧
      ∀ beta : Ordinal.{0}, 0 < beta → Ordinal.omega0 ^ beta < epsilonZero →
        (∀ rho ∈ word, actualProfileLeadingMonomial rho ≤ Ordinal.omega0 ^ beta) →
        ∀ n : Nat, z ≤ n →
          let initial := Ordinal.omega0 ^ beta * ((R : Nat) : Ordinal) + (n : Ordinal)
          actualFixedLimitProfileEval E z < actualTerminalValue initial ∧
          ∀ c : Nat,
            let g := compensatedPrefixControl c
            actualFixedLimitProfileEval E z < c + actualOrdinalNorm
              (actualControlledStateAfter g initial (actualControlledCount g initial))

end LogicLineages.OrdinalComparison.Targets
