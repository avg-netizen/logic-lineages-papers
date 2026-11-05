module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LeastSourceWitnessDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodecDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LeastSourceWitnessTargets
open CommonLayerSyntax LeastSourceWitness

def ScopeMonotonicity : Prop :=
  (∀ (small large : List Nat) (t : BaseTerm), (∀ i ∈ small, i ∈ large) →
    ScopedPhiParameters.termTest large t = true → ScopedPhiParameters.termTest small t = true) ∧
  (∀ (small large : List Nat) (p : SourceFormula), (∀ i ∈ small, i ∈ large) →
    ScopedPhiParameters.test large p = true → ScopedPhiParameters.test small p = true)

def ExistentialBodyAdmission : Prop := ∀ (i : Nat) (p : SourceFormula),
  FiniteSearchSource.test (.existsNat i p) = true → FiniteSearchSource.test p = true

def TotalNumericSearch : Prop := ∀ p : Input, (search p).Dom

def ExactNumericStatus : Prop := ∀ p : Input,
  (witness p).isSome = need p ∧ (need p = false → result p = 0)

def ActualLeastWitness : Prop := ∀ (values : List Nat) (i : Nat) (p : SourceFormula),
  FiniteSearchSource.test (.existsNat i p) = true → ∀ n : Nat,
    witness (values, i, p.encode) = some n ↔
      p.eval (Function.update (PlainParameterDecision.valuation values) i n) ∧
      ∀ m < n, ¬p.eval (Function.update (PlainParameterDecision.valuation values) i m)

def ActualNoWitness : Prop := ∀ (values : List Nat) (i : Nat) (p : SourceFormula),
  FiniteSearchSource.test (.existsNat i p) = true →
    (witness (values, i, p.encode) = none ↔
      ¬(SourceFormula.existsNat i p).eval (PlainParameterDecision.valuation values))

def ActualRawWitness : Prop := ∀ (values : List Nat) (i code : Nat),
  FiniteSearchPrograms.Code.test (parent (values, i, code)) = true → ∀ n : Nat,
    witness (values, i, code) = some n ↔
      (SourceFormulaCodec.decode code).eval (Function.update (PlainParameterDecision.valuation values) i n) ∧
      ∀ m < n, ¬(SourceFormulaCodec.decode code).eval (Function.update (PlainParameterDecision.valuation values) i m)

def ActualNumericPrograms : Prop :=
  Computable parent ∧ Computable need ∧ Computable₂ hit ∧ Partrec search ∧
  Computable result ∧ Computable witness

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LeastSourceWitnessTargets
