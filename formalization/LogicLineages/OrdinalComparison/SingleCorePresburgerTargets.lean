module
public import LogicLineages.OrdinalComparison.SingleCorePresburgerDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def ActualSingleCorePresburgerPrograms : Prop :=
  Computable (fun p : Nat × EncodedSingleCoreRow × Nat => encodedSingleCorePresburger p.1 p.2.1 p.2.2) ∧
  Computable (fun p : Nat × EncodedSingleCoreRow × List Nat => encodedSingleCoreUniversal p.1 p.2.1 p.2.2)

def ActualSingleCorePresburgerOutput : Prop := ∀ (d : Nat) (E : MultivariatePositiveExpr) (row : SingleCoreRow),
  multivariatePositiveValid d E → singleCoreRowValid row → ∀ desired : Nat,desired≤2 →
    ∃ formula : SingleCorePresburgerExpr,
      encodedSingleCorePresburger (multivariatePositiveEncode E) (singleCoreRowCode row) desired=
        singleCorePresburgerEncode formula ∧
      (∀ i∈singleCorePresburgerVariables formula,i∈singleCoreSupport E) ∧
      ∀ ρ : Nat → Nat,(∀ i : Nat,i<d → 0<ρ i) →
        (singleCorePresburgerValue formula ρ=true ↔
          singleCoreIntegerSign (actualSingleCoreRowValue row (actualMultivariatePositiveEval E ρ))=desired)

def ActualSingleCoreUniversal : Prop := ∀ (d : Nat) (E : MultivariatePositiveExpr) (row : SingleCoreRow),
  multivariatePositiveValid d E → singleCoreRowValid row → ∀ allowed : List Nat,
    encodedSingleCoreUniversal (multivariatePositiveEncode E) (singleCoreRowCode row) allowed=true ↔
      ∀ ρ : Nat → Nat,(∀ i : Nat,i<d → 0<ρ i) →
        singleCoreIntegerSign (actualSingleCoreRowValue row (actualMultivariatePositiveEval E ρ))∈allowed

/-- ENTIRE original08 thm:single-core: literal finite Presburger formulas on
the SAME original variables for each sign, actual arbitrary nested positive
core and integer row semantics, genuine all-code total Computable compiler,
and explicit universal sign-mask decision (covering equality/weak/strict).
No arithmetic-decision, core independence/range or finite-box oracle premise. -/
def FullActualSingleCorePresburger : Prop := ActualSingleCorePresburgerPrograms ∧
  ActualSingleCorePresburgerOutput ∧ ActualSingleCoreUniversal

end LogicLineages.OrdinalComparison.Targets
