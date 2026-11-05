module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchProgramsDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodecDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchProgramsTargets
open FiniteSearchPrograms

def LiteralSyntaxCode : Prop := ∀ p : SourceFormula, Code.test p.encode = FiniteSearchSource.test p

def LiteralAnswerCode : Prop := ∀ (values : List Nat) (p : SourceFormula),
  Code.answer values p.encode = FiniteSearchSource.answer values p

def LiteralDecisionCode : Prop := ∀ (values : List Nat) (p : SourceFormula),
  Code.decide values p.encode = FiniteSearchSource.decide values p

def ActualRawDecision : Prop := ∀ (values : List Nat) (code : Nat),
  (Code.decide values code).isSome = FiniteSearchSource.test (SourceFormulaCodec.decode code) ∧
  (FiniteSearchSource.test (SourceFormulaCodec.decode code) = true → ∀ b : Bool,
    Code.decide values code = some b ↔
      ((SourceFormulaCodec.decode code).eval (PlainParameterDecision.valuation values) ↔ b = true))

def ActualNumericPrograms : Prop :=
  Computable Code.test ∧ Computable₂ Code.answer ∧ Computable₂ Code.decide

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchProgramsTargets
