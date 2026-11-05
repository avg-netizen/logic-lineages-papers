module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveParameterDecisionDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveParameterDecisionTargets
open NormalForm

def PureOutputOccurrences : Prop := ∀ p : SourceFormula, AdditiveSource.test p = true →
  ∀ s ∈ LinearBlock.occurrences (AdditiveSource.eliminate p), ∃ i : Nat, s = Summand.variable i

def ExactDecisionDomain : Prop := ∀ (values : List Nat) (p : SourceFormula),
  (AdditiveParameterDecision.decide values p).isSome = AdditiveSource.test p

/-- Original Boolean and binder positions, including arbitrary alternation,
are retained only in the exact additive grammar. Every Phi node is rejected. -/
def ActualDecision : Prop := ∀ (values : List Nat) (p : SourceFormula), AdditiveSource.test p = true → ∀ b : Bool,
  AdditiveParameterDecision.decide values p = some b ↔
    (p.eval (PlainParameterDecision.valuation values) ↔ b = true)

def LiteralCodeDecision : Prop := ∀ (values : List Nat) (p : SourceFormula),
  AdditiveParameterDecision.Code.decide values p.encode = AdditiveParameterDecision.decide values p

def ActualNumericProgram : Prop := Primrec₂ AdditiveParameterDecision.Code.decide

def ActualRawDecision : Prop := ∀ (values : List Nat) (code : Nat),
  (AdditiveParameterDecision.Code.decide values code).isSome = AdditiveSource.test (SourceFormulaCodec.decode code) ∧
  (AdditiveSource.test (SourceFormulaCodec.decode code) = true → ∀ b : Bool,
    AdditiveParameterDecision.Code.decide values code = some b ↔
      ((SourceFormulaCodec.decode code).eval (PlainParameterDecision.valuation values) ↔ b = true))

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveParameterDecisionTargets
