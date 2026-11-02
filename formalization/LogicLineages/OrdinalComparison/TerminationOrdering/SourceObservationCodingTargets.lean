module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceObservationCodingDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceObservationCodingTargets
open Source Source.SourceOpenedObservations SourceObservationCoding

def TermCodeInjective : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty) (τ : Ty),
  Function.Injective (@termCode Symbol arity Γ τ)

def ObservationCodeInjective : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty) (B : Nat),
  Function.Injective (@observationCode Symbol arity Γ B)

def TermEqualCorrect : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (Γ : List Ty) (τ : Ty) (s t : Term Symbol arity Γ τ),termEqual s t=true ↔ s=t

def ObservationEqualCorrect : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (Γ : List Ty) (B : Nat) (o p : Observation Symbol arity Γ B),observationEqual o p=true ↔ o=p

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceObservationCodingTargets
