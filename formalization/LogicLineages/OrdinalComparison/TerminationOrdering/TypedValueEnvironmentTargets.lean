module
public import LogicLineages.OrdinalComparison.TerminationOrdering.TypedValueEnvironmentDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.TypedValueEnvironmentTargets
open Source Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment

def RestrictionIdentity : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (P : World I) (ρ : Environment I Γ P), @Eq (Environment I Γ P) (restrict (fun _ hp => hp) ρ) ρ

def RestrictionComposition : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (P Q R : World I) (h : Extends P Q) (k : Extends Q R) (ρ : Environment I Γ P), @Eq (Environment I Γ R) (restrict k (restrict h ρ)) (restrict (fun p hp => k p (h p hp)) ρ)

def RestrictionMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (P Q : World I) (h : Extends P Q) (ρ η : Environment I Γ P), EnvLE ρ η → EnvLE (restrict h ρ) (restrict h η)

def ExtensionMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (σ : Ty) (P : World I) (a b : Value I σ P) (ρ η : Environment I Γ P), a ≤ b → EnvLE ρ η → EnvLE (extend a ρ) (extend b η)

def ExtensionRestriction : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (σ : Ty) (P Q : World I) (h : Extends P Q) (a : Value I σ P) (ρ : Environment I Γ P), @Eq (Environment I (σ::Γ) Q) (restrict h (extend a ρ)) (extend (RecursiveNaturalDomains.weaken h a) (restrict h ρ))

def IdentityTransport : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (P Q : World I) (h : Extends P Q), @Eq (Environment I (portTypes P.val++I.context) Q) (restrict h (identity I P)) (reindex (LiteralVariableValue.extendVariables I.context Q.val P.val h) (identity I Q))

def ReindexRestriction : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ Δ : List Ty) (P Q : World I) (h : Extends P Q) (r : Renaming Γ Δ) (ρ : Environment I Δ P), @Eq (Environment I Γ Q) (restrict h (reindex r ρ)) (reindex r (restrict h ρ))

def ReindexLift : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ Δ : List Ty) (σ : Ty) (P : World I) (r : Renaming Γ Δ) (a : Value I σ P) (ρ : Environment I Δ P), @Eq (Environment I (σ::Γ) P) (reindex r.lift (extend a ρ)) (extend a (reindex r ρ))

end LogicLineages.OrdinalComparison.TerminationOrdering.TypedValueEnvironmentTargets
