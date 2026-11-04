module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundDoubleLambdaSubstitutionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundDoubleLambdaSubstitutionTargets
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative
open OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators PositiveArithmeticAccessibility PositiveArithmeticLeastSet
open SourceComputabilityFormula SourceApplicativeSubstitution

def ActualGroundDoubleLambdaSubstitution : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma Delta : List Ty)
    (context : Nat) (ctx : Context n) (scalarOld scalarInner scalarGround scalarBoth : Positive (Fin 2)) (beta tau : Ty),
  Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
  Calibrates scalarOld context (encodedScalar n arity Delta context) (encodedR n arity Delta context) →
  Calibrates scalarInner context (encodedScalar n arity (beta :: Delta) context) (encodedR n arity (beta :: Delta) context) →
  Calibrates scalarGround context (encodedScalar n arity (.ground :: Delta) context) (encodedR n arity (.ground :: Delta) context) →
  Calibrates scalarBoth context (encodedScalar n arity (beta :: .ground :: Delta) context) (encodedR n arity (beta :: .ground :: Delta) context) →
  ∀ theta : NumberedRewriteSyntax.Substitution (Fin n) arity Gamma Delta,
  NumberedUniverseBindingTargets.GoodSubstitution (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) theta →
  (∀ (upsilon : Ty) (v : Variable Gamma upsilon), Computable n arity Delta
    (fun x => x ∈ leastSet scalarOld context) context upsilon
    (representativeCode ctx.1.1 ctx.1.2 ⟨upsilon,theta v⟩)) →
  (∀ (upsilon : Ty) (v : Variable Gamma upsilon), Computable n arity (beta :: Delta)
    (fun x => x ∈ leastSet scalarInner context) context upsilon
    (representativeCode ctx.1.1 ctx.1.2 ⟨upsilon,rename (theta v) (Renaming.weaken Delta beta)⟩)) →
  (∀ (upsilon : Ty) (v : Variable Gamma upsilon), Computable n arity (.ground :: Delta)
    (fun x => x ∈ leastSet scalarGround context) context upsilon
    (representativeCode ctx.1.1 ctx.1.2 ⟨upsilon,rename (theta v) (Renaming.weaken Delta .ground)⟩)) →
  (∀ (upsilon : Ty) (v : Variable Gamma upsilon), Computable n arity (beta :: .ground :: Delta)
    (fun x => x ∈ leastSet scalarBoth context) context upsilon
    (representativeCode ctx.1.1 ctx.1.2 ⟨upsilon,rename (rename (theta v) (Renaming.weaken Delta .ground)) (Renaming.weaken (.ground :: Delta) beta)⟩)) →
  ∀ body : AuxTerm (Fin n) arity (beta :: .ground :: Gamma) tau,
  InUniverse ctx.1.1 ctx.1.2 (.lam (.lam body)) → ApplicativeFragment body →
  Computable n arity Delta (fun x => x ∈ leastSet scalarOld context) context (.arrow .ground (.arrow beta tau))
    (representativeCode ctx.1.1 ctx.1.2 ⟨.arrow .ground (.arrow beta tau),substitute (.lam (.lam body)) theta⟩)
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundDoubleLambdaSubstitutionTargets
