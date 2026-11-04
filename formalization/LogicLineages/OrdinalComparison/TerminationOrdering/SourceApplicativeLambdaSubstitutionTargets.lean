module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceApplicativeLambdaSubstitutionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceApplicativeLambdaSubstitutionTargets
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative
open OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators PositiveArithmeticAccessibility PositiveArithmeticLeastSet
open SourceComputabilityFormula SourceApplicativeSubstitution

def ActualApplicativeLambdaSubstitution : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma Delta : List Ty)
    (context : Nat) (ctx : Context n) (scalarOld scalarFresh : Positive (Fin 2)) (sigma tau : Ty),
  Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
  Calibrates scalarOld context (encodedScalar n arity Delta context) (encodedR n arity Delta context) →
  Calibrates scalarFresh context (encodedScalar n arity (sigma :: Delta) context) (encodedR n arity (sigma :: Delta) context) →
  ∀ theta : NumberedRewriteSyntax.Substitution (Fin n) arity Gamma Delta,
  NumberedUniverseBindingTargets.GoodSubstitution (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) theta →
  (∀ (upsilon : Ty) (v : Variable Gamma upsilon), Computable n arity Delta
    (fun x => x ∈ leastSet scalarOld context) context upsilon
    (representativeCode ctx.1.1 ctx.1.2 ⟨upsilon,theta v⟩)) →
  (∀ (upsilon : Ty) (v : Variable Gamma upsilon), Computable n arity (sigma :: Delta)
    (fun x => x ∈ leastSet scalarFresh context) context upsilon
    (representativeCode ctx.1.1 ctx.1.2 ⟨upsilon,rename (theta v) (Renaming.weaken Delta sigma)⟩)) →
  ∀ body : AuxTerm (Fin n) arity (sigma :: Gamma) tau,
  InUniverse ctx.1.1 ctx.1.2 (.lam body) → ApplicativeFragment body →
  Computable n arity Delta (fun x => x ∈ leastSet scalarOld context) context (.arrow sigma tau)
    (representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,substitute (.lam body) theta⟩)
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceApplicativeLambdaSubstitutionTargets
