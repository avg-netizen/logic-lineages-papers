module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceLambdaApplicativeSubstitutionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceLambdaApplicativeSubstitutionTargets
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative
open OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators PositiveArithmeticAccessibility PositiveArithmeticLeastSet
open SourceComputabilityFormula SourceLambdaApplicativeSubstitution

def ActualLambdaApplicativeComputableSubstitution : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma Delta : List Ty)
    (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2)),
  Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
  Calibrates scalar context (encodedScalar n arity Delta context) (encodedR n arity Delta context) →
  ∀ theta : NumberedRewriteSyntax.Substitution (Fin n) arity Gamma Delta,
  NumberedUniverseBindingTargets.GoodSubstitution (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) theta →
  (∀ (tau : Ty) (v : Variable Gamma tau),
    Computable n arity Delta (fun x => x ∈ leastSet scalar context) context tau
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,theta v⟩)) →
  ∀ (tau : Ty) (q : AuxTerm (Fin n) arity Gamma tau),
    InUniverse ctx.1.1 ctx.1.2 q → LambdaApplicativeFragment q →
    Computable n arity Delta (fun x => x ∈ leastSet scalar context) context tau
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,substitute q theta⟩)


end LogicLineages.OrdinalComparison.TerminationOrdering.SourceLambdaApplicativeSubstitutionTargets
