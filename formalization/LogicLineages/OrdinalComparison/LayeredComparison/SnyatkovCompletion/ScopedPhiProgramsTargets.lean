module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsTargets
open CommonLayerSyntax ScopedPhiPrograms

def ActualZeroDefaultEvaluation : Prop := ∀ (values : List Nat) (t : BaseTerm),
  Code.value values t.encode = t.value (PlainParameterDecision.valuation values)

def LiteralTermData : Prop :=
  (∀ (names : List Nat) (t : BaseTerm), Code.termTest names t.encode = ScopedPhiParameters.termTest names t) ∧
  (∀ (values : List Nat) (t : BaseTerm), Code.freezeTerm values t.encode =
    (ScopedPhiParameters.freezeTerm (PlainParameterDecision.valuation values) t).encode)

def LiteralFormulaData : Prop :=
  (∀ (names : List Nat) (p : SourceFormula), Code.test names p.encode = ScopedPhiParameters.test names p) ∧
  (∀ (values : List Nat) (p : SourceFormula), Code.freezeFormula values p.encode =
    (ScopedPhiParameters.freezeFormula (PlainParameterDecision.valuation values) p).encode)

def LiteralDecision : Prop := ∀ (values : List Nat) (p : SourceFormula),
  Code.decide values p.encode = ScopedPhiParameters.decide values p

def ActualRawDecision : Prop := ∀ (values : List Nat) (code : Nat),
  (Code.decide values code).isSome = ScopedPhiParameters.test [] (SourceFormulaCodec.decode code) ∧
  (ScopedPhiParameters.test [] (SourceFormulaCodec.decode code) = true → ∀ b : Bool,
    Code.decide values code = some b ↔
      ((SourceFormulaCodec.decode code).eval (PlainParameterDecision.valuation values) ↔ b = true))

/-- Actual total algorithms on every raw input. Full numeric effectivity is
Computable, not an asserted primitive-recursive bound or supplied evaluator. -/
def ActualNumericPrograms : Prop :=
  Primrec Code.bound ∧ Primrec₂ Code.table ∧ Computable₂ Code.value ∧
  Computable₂ Code.termTest ∧ Computable₂ Code.test ∧
  Computable₂ Code.freezeTerm ∧ Computable₂ Code.freezeFormula ∧ Computable₂ Code.decide

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsTargets
