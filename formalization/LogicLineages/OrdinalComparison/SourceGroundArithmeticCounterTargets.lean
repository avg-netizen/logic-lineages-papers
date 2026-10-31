module
public import LogicLineages.OrdinalComparison.SourceGroundArithmeticCounterDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundArithmeticCounter.Targets
open GroundEquivalence BooleanCompiler

def Pointwise : Prop := ∀ Γ (ρ : Variable Γ .ground → Nat) strict (a b : Input Γ .ground),
  Eval ρ (counter strict a b) ↔ ¬ RawQuery strict ρ a b

def Unsatisfiable : Prop := ∀ Γ strict (a b : Input Γ .ground),
  (¬ ∃ ρ : Variable Γ .ground → Nat, Eval ρ (counter strict a b)) ↔
    (if strict then Strict a.term b.term else Weak a.term b.term)

/-- At ground output all positive coordinates are exactly the original zero
padding, so the actual vector query has only its genuine scalar comparison. -/
def GroundQuery : Prop := ∀ Γ (ρ : Variable Γ .ground → Nat) strict (a b : Input Γ .ground),
  GroundPositiveQuerySplit.QueryAt strict a.term b.term (ExistentialPlan.inputs ρ) ↔ RawQuery strict ρ a b
end LogicLineages.OrdinalComparison.Source.GroundArithmeticCounter.Targets
