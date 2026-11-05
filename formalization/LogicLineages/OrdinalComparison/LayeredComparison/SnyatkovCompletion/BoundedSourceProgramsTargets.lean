module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProgramsDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodecDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProgramsTargets
open CommonLayerSyntax BoundedSourcePrograms

def ExactFiniteUpdate : Prop := ∀ (values : List Nat) (i n j : Nat),
  PlainParameterDecision.valuation (Code.update values i n) j =
    Function.update (PlainParameterDecision.valuation values) i n j

def LiteralGuardCode : Prop := ∀ (i : Nat) (p : SourceFormula),
  Code.guard i p.encode = (BoundedSource.guard i p).map BaseTerm.encode

def LiteralSyntaxCode : Prop := ∀ (p : SourceFormula), Code.test p.encode = BoundedSource.test p

def LiteralAnswerCode : Prop := ∀ (values : List Nat) (p : SourceFormula),
  Code.answer values p.encode = BoundedSource.answer (PlainParameterDecision.valuation values) p

def ActualRawDecision : Prop := ∀ (values : List Nat) (code : Nat),
  (Code.decide values code).isSome = BoundedSource.test (SourceFormulaCodec.decode code) ∧
  (BoundedSource.test (SourceFormulaCodec.decode code) = true → ∀ b : Bool,
    Code.decide values code = some b ↔
      ((SourceFormulaCodec.decode code).eval (PlainParameterDecision.valuation values) ↔ b = true))

def ActualNumericPrograms : Prop :=
  Primrec (fun p : List Nat × (Nat × Nat) => Code.update p.1 p.2.1 p.2.2) ∧
  Computable₂ Code.guard ∧ Computable Code.test ∧ Computable₂ Code.answer ∧ Computable₂ Code.decide

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProgramsTargets
