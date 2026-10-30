module
public import LogicLineages.OrdinalComparison.PositiveUnaryIdentityDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- Exact P1 specialization only, not the multivariate source identity theorem. -/
def ActualPositiveUnaryIdentity : Prop :=
  Computable₂ encodedPositiveNormalFormsEqual ∧ Computable₂ encodedPositiveZeroBound ∧
  Computable₂ encodedPositiveCounterInput ∧
  ∀ E F : FixedLimitPositiveExpr,
    fixedLimitProfileBelow epsilonZero E → fixedLimitProfileBelow epsilonZero F →
    let n := positiveExprEncode E
    let m := positiveExprEncode F
    let k := encodedPositiveZeroBound n m
    let v := encodedPositiveCounterInput n m
    1≤k ∧ v=Phi k+1 ∧ 0<v ∧
    (encodedPositiveNormalFormsEqual n m=true ↔
      ∀ x : Nat, 0<x → actualFixedLimitProfileEval E x=actualFixedLimitProfileEval F x) ∧
    (encodedPositiveNormalFormsEqual n m=false →
      actualFixedLimitProfileEval E v≠actualFixedLimitProfileEval F v)

end LogicLineages.OrdinalComparison.Targets
