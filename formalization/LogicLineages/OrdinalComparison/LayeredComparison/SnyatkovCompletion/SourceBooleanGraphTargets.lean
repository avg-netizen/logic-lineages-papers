module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanGraphDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanGraphTargets
open CommonLayerSyntax NormalForm SourceTermGraph SourceBooleanGraph

def LiteralForestVariables : Prop := ∀ p : SourceFormula, test p = true →
  (forest p).variables = p.variables

def ActualPredicateInterpretation : Prop := ∀ (p : SourceFormula) (s : Nat) (ν : Nat → Nat),
  test p = true → (graph s (forest p)).eval ν → ((predicate s p).eval ν ↔ p.eval ν)

def PlainCompiledMatrix : Prop := ∀ (p : SourceFormula) (s : Nat),
  MaximalPlainBranch.isPlain (matrix s p) = true

def ActualExistentialMatrix : Prop := ∀ (p : SourceFormula) (ν : Nat → Nat),
  test p = true →
    (existsPrefix ν (allocated (start p) (forest p)) (compile p) ↔ p.eval ν)

def ActualSatisfiabilityTranslation : Prop := ∀ p : SourceFormula, test p = true →
  (PlainLinearCleanup.Satisfiable (compile p) ↔ ∃ ν : Nat → Nat, p.eval ν)

def ExactDecisionDomain : Prop := ∀ p : SourceFormula,
  (decideExists p).isSome = test p ∧ (decideForall p).isSome = test p

def ActualExistentialDecision : Prop := ∀ p : SourceFormula, test p = true → ∀ b : Bool,
  decideExists p = some b ↔ ((∃ ν : Nat → Nat, p.eval ν) ↔ b = true)

def ActualUniversalDecision : Prop := ∀ p : SourceFormula, test p = true → ∀ b : Bool,
  decideForall p = some b ↔ ((∀ ν : Nat → Nat, p.eval ν) ↔ b = true)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanGraphTargets
