module
public import LogicLineages.OrdinalComparison.SourceDecisionEquivalenceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.DecisionEquivalence.Targets
open GroundEquivalence

/-- Whole source decision equivalence, using the concrete complete A-normal
arithmetic/Boolean DAG encoding. Uniform effectivity is factored explicitly:
source requests are unchanged numeric source codes; numericData is Computable;
all three total finite syntax templates above are executable definitions with
no noncomputable operation. Actual reductions are exactly their compositions.
No decidability of any of these equivalent problems is asserted. -/
def FullDecisionEquivalence : Prop :=
  Computable numericData ∧
  (∀ Γ τ υ (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) strict (a : Input Γ τ) (b : Input Γ υ)
      (ρ : Variable Γ .ground → Nat),
    ExistentialPlan.Eval ρ (realize hΓ strict a b) ↔
      ¬ GroundPositiveQuerySplit.QueryAt strict a.term b.term (ExistentialPlan.inputs ρ)) ∧
  (∀ Γ τ υ (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) strict (a : Input Γ τ) (b : Input Γ υ),
    (∀ σ ∈ (toStrict hΓ strict a b).context, σ=Ty.ground) ∧
    (∀ σ ∈ (toWeak hΓ strict a b).context, σ=Ty.ground) ∧
    (Universal strict a b ↔ Strict (toStrict hΓ strict a b).left.term (toStrict hΓ strict a b).right.term) ∧
    (Universal strict a b ↔ Weak (toWeak hΓ strict a b).left.term (toWeak hΓ strict a b).right.term) ∧
    (Universal strict a b ↔ ¬ ∃ ρ, BooleanCompiler.Eval ρ (toArithmetic hΓ strict a b).program)) ∧
  (∀ Γ (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) strict (a b : Input Γ .ground),
    Universal strict a b ↔ if strict then Strict a.term b.term else Weak a.term b.term) ∧
  ∀ Γ (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (p : BooleanCompiler.Program Γ),
    (∀ σ ∈ (ExistentialPlan.compile (BooleanCompiler.lower p)).context, σ=Ty.ground) ∧
    ((¬ ∃ ρ, BooleanCompiler.Eval ρ p) ↔
      Strict (BooleanCompiler.strictPair p).1.term (BooleanCompiler.strictPair p).2.term) ∧
    ((¬ ∃ ρ, BooleanCompiler.Eval ρ p) ↔
      Weak (BooleanCompiler.weakPair p).1.term (BooleanCompiler.weakPair p).2.term) ∧
    ((∃ ρ, BooleanCompiler.Eval ρ p) ↔
      ¬ Strict (BooleanCompiler.strictPair p).1.term (BooleanCompiler.strictPair p).2.term)
end LogicLineages.OrdinalComparison.Source.DecisionEquivalence.Targets
