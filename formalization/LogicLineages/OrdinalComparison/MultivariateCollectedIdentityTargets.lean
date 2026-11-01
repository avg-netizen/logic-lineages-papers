module
public import LogicLineages.OrdinalComparison.MultivariateCollectedTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- Complete semantic equality for the ACTUAL coefficient-vector/dictionary
outputs under any shared finite source signature. The bound is a numeric
syntax bound, not a supplied semantic certificate. This does not silently
assert cap independence or the missing uniform numeric decoder. -/
def MultivariateCollectedCommonSignatureIdentity : Prop :=
  ∀ (d cap : Nat) (E F : MultivariatePositiveExpr),
    multivariatePositiveValid d E → multivariatePositiveValid d F →
    multivariatePositiveEncode E≤cap → multivariatePositiveEncode F≤cap →
      (multivariateCollectedNormalizeAt cap E=multivariateCollectedNormalizeAt cap F ↔
        ∀ rho : Nat → Nat, (∀ i : Nat, i<d → 0<rho i) →
          actualMultivariatePositiveEval E rho=actualMultivariatePositiveEval F rho)

end LogicLineages.OrdinalComparison.Targets
