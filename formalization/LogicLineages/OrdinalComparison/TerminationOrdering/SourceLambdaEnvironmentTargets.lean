module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceLambdaEnvironmentDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceLambdaEnvironmentTargets
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative
open OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators PositiveArithmeticAccessibility PositiveArithmeticLeastSet
open SourceComputabilityFormula SourceLambdaEnvironment

def ActualArgumentEnvironment : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma Delta : List Ty)
    (context : Nat) (ctx : Context n) (P : Nat → Prop) (sigma : Ty)
    (theta : NumberedRewriteSyntax.Substitution (Fin n) arity Gamma Delta) (a : AuxTerm (Fin n) arity Delta sigma),
  NumberedUniverseBindingTargets.GoodSubstitution (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) theta →
  InUniverse ctx.1.1 ctx.1.2 a →
  (∀ (tau : Ty) (v : Variable Gamma tau), Computable n arity Delta P context tau
    (representativeCode ctx.1.1 ctx.1.2 ⟨tau,theta v⟩)) →
  Computable n arity Delta P context sigma (representativeCode ctx.1.1 ctx.1.2 ⟨sigma,a⟩) →
  NumberedUniverseBindingTargets.GoodSubstitution (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) (extend theta a) ∧
  ∀ (tau : Ty) (v : Variable (sigma :: Gamma) tau), Computable n arity Delta P context tau
    (representativeCode ctx.1.1 ctx.1.2 ⟨tau,extend theta a v⟩)

def ActualFreshEnvironment : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma Delta : List Ty)
    (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2)) (sigma : Ty),
  Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) → sigma ∈ ctx.1.2 →
  Calibrates scalar context (encodedScalar n arity (sigma :: Delta) context) (encodedR n arity (sigma :: Delta) context) →
  ∀ theta : NumberedRewriteSyntax.Substitution (Fin n) arity Gamma Delta,
  NumberedUniverseBindingTargets.GoodSubstitution (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) theta →
  (∀ (tau : Ty) (v : Variable Gamma tau), Computable n arity (sigma :: Delta)
    (fun x => x ∈ leastSet scalar context) context tau
    (representativeCode ctx.1.1 ctx.1.2 ⟨tau,rename (theta v) (Renaming.weaken Delta sigma)⟩)) →
  NumberedUniverseBindingTargets.GoodSubstitution (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2)
    (liftSubstitution (sigma := sigma) theta) ∧
  ∀ (tau : Ty) (v : Variable (sigma :: Gamma) tau), Computable n arity (sigma :: Delta)
    (fun x => x ∈ leastSet scalar context) context tau
    (representativeCode ctx.1.1 ctx.1.2 ⟨tau,liftSubstitution theta v⟩)

def ActualExtendedBetaIdentity : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma Delta : List Ty)
    (sigma tau : Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (body : AuxTerm Symbol arity (sigma :: Gamma) tau) (a : AuxTerm Symbol arity Delta sigma),
  substitute (substitute body (liftSubstitution theta)) (singleSubstitution a) = substitute body (extend theta a)
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceLambdaEnvironmentTargets
