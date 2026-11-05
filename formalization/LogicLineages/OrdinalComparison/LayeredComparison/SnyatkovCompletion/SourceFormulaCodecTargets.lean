module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodecDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodecTargets
open SourceFormulaCodec

def SourceRoundtrip : Prop := ∀ p : SourceFormula, decode p.encode = p

def CodeRoundtrip : Prop := ∀ code : Nat, (decode code).encode = code

def LiteralRawPayload : Prop := ∀ code : Nat,
  SourceBooleanPrograms.Code.payload code = (SourceBooleanGraph.test (decode code),
    (SourceBooleanGraph.forest (decode code)).encode, (SourceBooleanGraph.predicate 0 (decode code)).encode)

def ExactRawDecisionDomain : Prop := ∀ (xs values : List Nat) (code : Nat),
  (SourceParameterDecision.Code.decideExists xs values code).isSome = SourceBooleanGraph.test (decode code) ∧
    (SourceParameterDecision.Code.decideForall xs values code).isSome = SourceBooleanGraph.test (decode code)

def ActualRawDecisions : Prop := ∀ (xs values : List Nat) (code : Nat),
  SourceBooleanGraph.test (decode code) = true → ∀ b : Bool,
  (SourceParameterDecision.Code.decideExists xs values code = some b ↔
    ((SourceParameterDecision.existsBind xs (decode code)).eval (PlainParameterDecision.valuation values) ↔ b = true)) ∧
  (SourceParameterDecision.Code.decideForall xs values code = some b ↔
    ((SourceParameterDecision.forallBind xs (decode code)).eval (PlainParameterDecision.valuation values) ↔ b = true))

def ActualRawNumericPrograms : Prop :=
  Primrec (fun p : List Nat × (List Nat × Nat) => SourceParameterDecision.Code.decideExists p.1 p.2.1 p.2.2) ∧
    Primrec (fun p : List Nat × (List Nat × Nat) => SourceParameterDecision.Code.decideForall p.1 p.2.1 p.2.2)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodecTargets
