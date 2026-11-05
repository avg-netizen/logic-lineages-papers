module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceParameterDecisionDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceParameterDecisionTargets
open CommonLayerSyntax SourceParameterDecision

def ActualBlockTranslation : Prop := ∀ (xs : List Nat) (p : SourceFormula) (ν : Nat → Nat),
  SourceBooleanGraph.test p = true →
    (NormalForm.existsPrefix ν (xs ++ witnesses p) (SourceBooleanGraph.compile p) ↔ (existsBind xs p).eval ν)

def ExactDecisionDomain : Prop := ∀ (xs values : List Nat) (p : SourceFormula),
  (decideExists xs values p).isSome = SourceBooleanGraph.test p ∧
    (decideForall xs values p).isSome = SourceBooleanGraph.test p

def ActualSourceDecisions : Prop := ∀ (xs values : List Nat) (p : SourceFormula),
  SourceBooleanGraph.test p = true → ∀ b : Bool,
  (decideExists xs values p = some b ↔ ((existsBind xs p).eval (PlainParameterDecision.valuation values) ↔ b = true)) ∧
    (decideForall xs values p = some b ↔ ((forallBind xs p).eval (PlainParameterDecision.valuation values) ↔ b = true))

def LiteralWitnesses : Prop := ∀ p : SourceFormula, Code.witnesses p.encode = witnesses p

def LiteralDecisions : Prop := ∀ (xs values : List Nat) (p : SourceFormula),
  Code.decideExists xs values p.encode = decideExists xs values p ∧
    Code.decideForall xs values p.encode = decideForall xs values p

def ActualNumericPrograms : Prop :=
  Primrec Code.witnesses ∧
    Primrec (fun p : List Nat × (List Nat × Nat) => Code.decideExists p.1 p.2.1 p.2.2) ∧
    Primrec (fun p : List Nat × (List Nat × Nat) => Code.decideForall p.1 p.2.1 p.2.2)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceParameterDecisionTargets
