module
public import LogicLineages.OrdinalComparison.MultivariateIdentitySourceDefinitions
public import LogicLineages.OrdinalComparison.OneVariableComparisonDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.StandardControlCurrent.IdentitySignTargets
open OrdinalComparison

/-- Complete current18 u:thm:identity, including literal NF output and positive weighted-Phi countervaluation. -/
def IdentityNormalForm : Prop :=
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

/-- Complete current18 u:thm:sign on the actual two-sort source grammar, with genuine-domain tail. -/
def EventualSigns : Prop :=
  ∃ decision : Nat → Nat → Nat × Nat, Computable₂ decision ∧
    ∀ E F : OneVariableComparisonExpr, oneVariableComparisonValid E → oneVariableComparisonValid F →
      let result := decision (oneVariableComparisonEncode E) (oneVariableComparisonEncode F)
      result.1≤2 ∧ 1≤result.2 ∧ ∀ x : Nat, result.2≤x →
        oneVariableComparisonDomainAt E x ∧ oneVariableComparisonDomainAt F x ∧
        (result.1=0 ↔ actualOneVariableComparisonValue E x<actualOneVariableComparisonValue F x) ∧
        (result.1=1 ↔ actualOneVariableComparisonValue E x=actualOneVariableComparisonValue F x) ∧
        (result.1=2 ↔ actualOneVariableComparisonValue F x<actualOneVariableComparisonValue E x)

end LogicLineages.StandardControlCurrent.IdentitySignTargets
