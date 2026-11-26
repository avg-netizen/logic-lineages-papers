module
public import LogicLineages.OrdinalComparison.SingleCorePresburgerDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.StandardControlCurrent.SingleCoreTargets
open OrdinalComparison

/-- Actual all-code compiler and universal comparison program, not a supplied
Presburger or eventual-sign oracle. -/
def Programs : Prop :=
  Computable (fun p : Nat × EncodedSingleCoreRow × Nat =>
    encodedSingleCorePresburger p.1 p.2.1 p.2.2) ∧
  Computable (fun p : Nat × EncodedSingleCoreRow × List Nat =>
    encodedSingleCoreUniversal p.1 p.2.1 p.2.2)

/-- Each of the three sign predicates of the literal signed single-core row
has actual finite Presburger syntax on the original correlated raw names.
Core nesting and fixed nonzero limit heads are arbitrary below epsilonZero. -/
def SignFormulas : Prop :=
  ∀ (d : Nat) (E : MultivariatePositiveExpr) (row : SingleCoreRow),
    multivariatePositiveValid d E → singleCoreRowValid row →
    ∀ desired : Nat, desired ≤ 2 →
      ∃ formula : SingleCorePresburgerExpr,
        encodedSingleCorePresburger (multivariatePositiveEncode E)
          (singleCoreRowCode row) desired = singleCorePresburgerEncode formula ∧
        (∀ i ∈ singleCorePresburgerVariables formula, i ∈ singleCoreSupport E) ∧
        ∀ ρ : Nat → Nat, (∀ i : Nat, i < d → 0 < ρ i) →
          (singleCorePresburgerValue formula ρ = true ↔
            singleCoreIntegerSign
              (actualSingleCoreRowValue row (actualMultivariatePositiveEval E ρ)) = desired)

/-- Closed universal sign-mask decision includes strict, weak, and equality.
No hypothesis asserts independence, surjectivity, balanced certificates, or
bounded range of the arbitrary core. -/
def UniversalComparison : Prop :=
  ∀ (d : Nat) (E : MultivariatePositiveExpr) (row : SingleCoreRow),
    multivariatePositiveValid d E → singleCoreRowValid row →
    ∀ allowed : List Nat,
      encodedSingleCoreUniversal (multivariatePositiveEncode E)
        (singleCoreRowCode row) allowed = true ↔
        ∀ ρ : Nat → Nat, (∀ i : Nat, i < d → 0 < ρ i) →
          singleCoreIntegerSign
            (actualSingleCoreRowValue row (actualMultivariatePositiveEval E ρ)) ∈ allowed

/-- Full current18 m:thm:single-core; no general polynomial QE claim. -/
def FullSingleCore : Prop := Programs ∧ SignFormulas ∧ UniversalComparison

end LogicLineages.StandardControlCurrent.SingleCoreTargets
