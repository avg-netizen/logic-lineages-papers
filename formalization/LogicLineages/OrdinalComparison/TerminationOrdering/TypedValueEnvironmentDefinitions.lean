module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorIterationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.TypedValueEnvironment
open Source Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains

abbrev Environment {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (Γ : List Ty) (P : World I) := {τ : Ty} → Variable Γ τ → Value I τ P

def EnvLE {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {Γ : List Ty} {P : World I}
    (ρ η : Environment I Γ P) : Prop := ∀ {τ} (v : Variable Γ τ),ρ v ≤ η v

def restrict {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {Γ : List Ty} {P Q : World I}
    (h : Extends P Q) (ρ : Environment I Γ P) : Environment I Γ Q := fun v => RecursiveNaturalDomains.weaken h (ρ v)

def extend {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {Γ : List Ty} {P : World I} {σ : Ty}
    (a : Value I σ P) (ρ : Environment I Γ P) : Environment I (σ::Γ) P := fun v => match v with
  | .here => a
  | .there v => ρ v

def reindex {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {Γ Δ : List Ty} {P : World I}
    (r : Renaming Γ Δ) (ρ : Environment I Δ P) : Environment I Γ P := fun v => ρ (r v)

def identity {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (P : World I) : Environment I (portTypes P.val++I.context) P :=
  fun v => LiteralVariableValueProof.variableValue v

end LogicLineages.OrdinalComparison.TerminationOrdering.TypedValueEnvironment
