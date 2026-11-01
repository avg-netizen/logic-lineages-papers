module
public import LogicLineages.OrdinalComparison.MultivariateIdentitySourceDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- ENTIRE original paper07 thm:identity, on the literal P_d grammar with
actual canonical nonzero-limit heads below epsilon0. Includes actual finite
coefficient-vector/original-head recursive dictionary, all grammar invariants,
source-value preservation, uniform computable NF OUTPUT and literal code
comparison, universal identity completeness and an effective strictly
positive weighted-Phi countervaluation. No supplied normal-form/semantic/
compiler-success/termination certificate is an extra source premise. -/
def FullActualMultivariateIdentity : Prop :=
  Computable encodedMultivariateCollectedNormalize ∧
  Computable₂ encodedMultivariateLiteralIdentity ∧
  Computable₂ encodedMultivariatePhiCounterIndex ∧
  Computable (fun p : Nat × Nat × Nat => encodedMultivariateCounterWeight p.1 p.2.1 p.2.2) ∧
  ∀ (d : Nat) (E F : MultivariatePositiveExpr),
    multivariatePositiveValid d E → multivariatePositiveValid d F →
    let n := multivariatePositiveEncode E
    let m := multivariatePositiveEncode F
    let A := multivariateCollectedNormalize E
    let B := multivariateCollectedNormalize F
    let k := encodedMultivariatePhiCounterIndex n m
    encodedMultivariateCollectedNormalize n=multivariateCollectedCode A ∧
    encodedMultivariateCollectedNormalize m=multivariateCollectedCode B ∧
    MultivariateCollectedValid d A ∧ MultivariateCollectedValid d B ∧
    (∀ rho : Nat → Nat, actualMultivariateCollectedValue A rho=actualMultivariatePositiveEval E rho) ∧
    (∀ rho : Nat → Nat, actualMultivariateCollectedValue B rho=actualMultivariatePositiveEval F rho) ∧
    (encodedMultivariateLiteralIdentity n m=true ↔ A=B) ∧
    (A=B ↔ ∀ rho : Nat → Nat, (∀ i : Nat, i<d → 0<rho i) →
      actualMultivariatePositiveEval E rho=actualMultivariatePositiveEval F rho) ∧
    (A≠B → 1≤k ∧ (∀ i : Nat, 0<encodedMultivariateCounterWeight n m i) ∧
      actualMultivariatePositiveEval E (fun i => encodedMultivariateCounterWeight n m i*(Phi k+1))≠
        actualMultivariatePositiveEval F (fun i => encodedMultivariateCounterWeight n m i*(Phi k+1)))

end LogicLineages.OrdinalComparison.Targets
