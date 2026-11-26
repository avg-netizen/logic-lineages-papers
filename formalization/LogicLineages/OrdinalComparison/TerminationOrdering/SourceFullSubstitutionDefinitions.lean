module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceLambdaEnvironmentDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceRankedConstructorComputabilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceFullSubstitution
open Source NumberedRewriteSyntax NumberedLeastCodeRepresentative OrdinaryArithmeticQuotient
open PositiveArithmeticOperators PositiveArithmeticLeastSet SourceComputabilityFormula

/-- Actual computability of substitution images at types occurring in the fixed
finite universe. This matches the guard in GoodSubstitution and imposes no
condition on unused source-context types outside that universe. -/
def WindowComputableEnvironment (n : Nat) (arity : Fin n → Nat)
    (Gamma Delta : List Ty) (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2))
    (theta : NumberedRewriteSyntax.Substitution (Fin n) arity Gamma Delta) : Prop :=
  ∀ (tau : Ty) (v : Variable Gamma tau), tau ∈ ctx.1.2 →
    Computable n arity Delta (fun x => x ∈ leastSet scalar context) context tau
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,theta v⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceFullSubstitution
