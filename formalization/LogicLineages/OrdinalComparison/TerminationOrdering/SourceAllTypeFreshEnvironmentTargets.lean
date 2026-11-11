module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceAllTypeFreshEnvironmentDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceAllTypeFreshEnvironmentTargets
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative
open OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators PositiveArithmeticAccessibility PositiveArithmeticLeastSet
open SourceComputabilityFormula SourceLambdaEnvironment

/-- Retains the original fresh-variable membership and GoodSubstitution guards.
The weakened-image computability premise of ActualFreshEnvironment is derived,
not assumed. Both scalar operators calibrate the same finite decoded context. -/
def ActualFreshEnvironmentFromComputable : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma Delta : List Ty)
    (context : Nat) (ctx : Context n) (scalarOld scalarNew : Positive (Fin 2)) (sigma : Ty),
  Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) → sigma ∈ ctx.1.2 →
  Calibrates scalarOld context (encodedScalar n arity Delta context) (encodedR n arity Delta context) →
  Calibrates scalarNew context (encodedScalar n arity (sigma :: Delta) context) (encodedR n arity (sigma :: Delta) context) →
  ∀ theta : NumberedRewriteSyntax.Substitution (Fin n) arity Gamma Delta,
  NumberedUniverseBindingTargets.GoodSubstitution (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) theta →
  (∀ (tau : Ty) (v : Variable Gamma tau), Computable n arity Delta
    (fun x => x ∈ leastSet scalarOld context) context tau
    (representativeCode ctx.1.1 ctx.1.2 ⟨tau,theta v⟩)) →
  NumberedUniverseBindingTargets.GoodSubstitution (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2)
    (liftSubstitution (sigma := sigma) theta) ∧
  ∀ (tau : Ty) (v : Variable (sigma :: Gamma) tau), Computable n arity (sigma :: Delta)
    (fun x => x ∈ leastSet scalarNew context) context tau
    (representativeCode ctx.1.1 ctx.1.2 ⟨tau,liftSubstitution theta v⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceAllTypeFreshEnvironmentTargets
