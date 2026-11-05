module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceTargets
open BaseBooleanSource

def ExactTranslation : Prop := ∀ (p : BaseFormula.Formula) (ν : Nat → Nat),
  (translate p).eval ν ↔ p.eval ν

def ExactSourceData : Prop := ∀ p : BaseFormula.Formula,
  SourceBooleanGraph.test (translate p) = true ∧ (translate p).variables = p.variables

def ExactPrefixTranslation : Prop := ∀ (xs : List Nat) (p : BaseFormula.Formula) (ν : Nat → Nat),
  ((SourceParameterDecision.existsBind xs (translate p)).eval ν ↔ existsPrefix ν xs p) ∧
    ((SourceParameterDecision.forallBind xs (translate p)).eval ν ↔ forallPrefix ν xs p)

def LiteralStackCompiler : Prop := ∀ (p : BaseFormula.Formula) (stack : List Nat),
  Code.run p.encode stack = (translate p).encode :: stack

def LiteralCompiler : Prop := ∀ p : BaseFormula.Formula, Code.compile p.encode = (translate p).encode

def ActualBlockDecisions : Prop := ∀ (xs values : List Nat) (p : BaseFormula.Formula) (b : Bool),
  (Code.decideExists xs values p.encode = some b ↔ (existsPrefix (PlainParameterDecision.valuation values) xs p ↔ b = true)) ∧
    (Code.decideForall xs values p.encode = some b ↔ (forallPrefix (PlainParameterDecision.valuation values) xs p ↔ b = true))

def ActualClosureDecisions : Prop := ∀ (p : BaseFormula.Formula) (b : Bool),
  (Code.decideClosureExists p.encode = some b ↔ ((∃ ν : Nat → Nat, p.eval ν) ↔ b = true)) ∧
    (Code.decideClosureForall p.encode = some b ↔ ((∀ ν : Nat → Nat, p.eval ν) ↔ b = true))

def ActualNumericPrograms : Prop :=
  Primrec₂ Code.step ∧ Primrec₂ Code.run ∧ Primrec Code.compile ∧
  Primrec (fun p : List Nat × (List Nat × List CommonHeadCompiler.Instruction) => Code.decideExists p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : List Nat × (List Nat × List CommonHeadCompiler.Instruction) => Code.decideForall p.1 p.2.1 p.2.2) ∧
  Primrec Code.decideClosureExists ∧ Primrec Code.decideClosureForall

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceTargets
