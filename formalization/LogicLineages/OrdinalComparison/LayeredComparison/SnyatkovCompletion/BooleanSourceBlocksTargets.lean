module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BooleanSourceBlocksDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BooleanSourceBlocksTargets
open BooleanSourceBlocks

def ExactDecisionDomain : Prop := ∀ (values : List Nat) (p : SourceFormula),
  (BooleanSourceBlocks.decide values p).isSome = admissible p

def ActualDecision : Prop := ∀ (values : List Nat) (p : SourceFormula), admissible p = true → ∀ b : Bool,
  BooleanSourceBlocks.decide values p = some b ↔
    (p.eval (PlainParameterDecision.valuation values) ↔ b = true)

def LiteralCodeDecision : Prop := ∀ (values : List Nat) (p : SourceFormula),
  Code.decide values p.encode = BooleanSourceBlocks.decide values p

def ActualNumericProgram : Prop := Primrec₂ Code.decide

def ActualRawDecision : Prop := ∀ (values : List Nat) (code : Nat),
  (Code.decide values code).isSome = admissible (SourceFormulaCodec.decode code) ∧
  (admissible (SourceFormulaCodec.decode code) = true → ∀ b : Bool,
    Code.decide values code = some b ↔
      ((SourceFormulaCodec.decode code).eval (PlainParameterDecision.valuation values) ↔ b = true))

/-- Exact supported extension and explicit rejection of both leading mixed
alternation patterns, without changing the existing literal block recognizer. -/
def FragmentBoundary : Prop :=
  (∀ p : SourceFormula, HomogeneousSource.admissible p = true → admissible p = true) ∧
  (∀ p : SourceFormula, admissible p = true → admissible (.negative p) = true) ∧
  (∀ p q : SourceFormula, admissible p = true → admissible q = true → admissible (.conjunction p q) = true) ∧
  (∀ (i j : Nat) (p : SourceFormula),
    admissible (.existsNat i (.negative (.existsNat j p))) = false ∧
    admissible (.negative (.existsNat i (.negative (.existsNat j p)))) = false)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BooleanSourceBlocksTargets
