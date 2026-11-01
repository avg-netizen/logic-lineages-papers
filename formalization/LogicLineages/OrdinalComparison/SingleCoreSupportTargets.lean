module
public import LogicLineages.OrdinalComparison.SingleCoreSupportDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def ActualSingleCoreSupportProgram : Prop := Primrec encodedSingleCoreSupport ∧
  ∀ E : MultivariatePositiveExpr,encodedSingleCoreSupport (multivariatePositiveEncode E)=singleCoreSupport E

def ActualSingleCoreSupportBounds : Prop := ∀ (d : Nat) (E : MultivariatePositiveExpr),
  multivariatePositiveValid d E → ∀ i∈singleCoreSupport E,i<d ∧ i≤multivariatePositiveEncode E

def ActualSingleCoreSupportAgreement : Prop := ∀ (E : MultivariatePositiveExpr) (ρ σ : Nat → Nat),
  (∀ i∈singleCoreSupport E,ρ i=σ i) → actualMultivariatePositiveEval E ρ=actualMultivariatePositiveEval E σ

def ActualSingleCoreSupportDominance : Prop := ∀ (d : Nat) (E : MultivariatePositiveExpr),
  multivariatePositiveValid d E → ∀ (ρ : Nat → Nat) (i : Nat),i∈singleCoreSupport E →
    ρ i≤actualMultivariatePositiveEval E ρ

/-- Source08 section10's ACTUAL arbitrary nested core, with effective support,
value independence off that support and every supported raw-input dominance
proved. This is a supplier, not the full Presburger output compiler. -/
def FullActualSingleCoreSupport : Prop := ActualSingleCoreSupportProgram ∧ ActualSingleCoreSupportBounds ∧
  ActualSingleCoreSupportAgreement ∧ ActualSingleCoreSupportDominance

end LogicLineages.OrdinalComparison.Targets
