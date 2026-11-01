module
public import LogicLineages.OrdinalComparison.MultivariateDirectNormalizeDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def MultivariateClosedFoldProgram : Prop :=
  Computable encodedMultivariateClosedValue ∧
  ∀ E : MultivariatePositiveExpr,
    encodedMultivariateClosedValue (multivariatePositiveEncode E)=actualMultivariatePositiveEval E (fun _ => 0)

/-- Exact syntactic correspondence, not merely equal ordinal semantics. -/
def MultivariateDirectNormalizeCorrespondence : Prop :=
  ∀ (d cap : Nat) (E : MultivariatePositiveExpr), multivariatePositiveValid d E →
    multivariatePositiveEncode E≤cap →
      multivariateCollectedNormalizeAt cap E=multivariateCollectedNormalize E

def MultivariateDirectNormalizeSource : Prop :=
  ∀ (d : Nat) (E : MultivariatePositiveExpr), multivariatePositiveValid d E →
    ∀ rho : Nat → Nat,
      actualMultivariateCollectedValue (multivariateCollectedNormalize E) rho=
        actualMultivariatePositiveEval E rho

def MultivariateDirectNormalizeComplete : Prop :=
  ∀ (d : Nat) (E F : MultivariatePositiveExpr),
    multivariatePositiveValid d E → multivariatePositiveValid d F →
      (multivariateCollectedNormalize E=multivariateCollectedNormalize F ↔
        ∀ rho : Nat → Nat, (∀ i : Nat, i<d → 0<rho i) →
          actualMultivariatePositiveEval E rho=actualMultivariatePositiveEval F rho)

def MultivariateCollectedCapIndependent : Prop :=
  ∀ (d cap cap' : Nat) (E : MultivariatePositiveExpr), multivariatePositiveValid d E →
    multivariatePositiveEncode E≤cap → multivariatePositiveEncode E≤cap' →
      multivariateCollectedNormalizeAt cap E=multivariateCollectedNormalizeAt cap' E

end LogicLineages.OrdinalComparison.Targets
