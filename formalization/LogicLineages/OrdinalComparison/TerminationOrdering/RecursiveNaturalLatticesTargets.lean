module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveNaturalLatticesDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveNaturalLatticesTargets
open Source FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains RecursiveNaturalLattices

def CompleteDomains : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (τ : Ty) (P : World I),CompleteAt I τ P

def SupremumExistence : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (τ : Ty) (P : World I) (S : Set (Value I τ P)),∃ a,IsLUB S a

def InfimumExistence : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (τ : Ty) (P : World I) (S : Set (Value I τ P)),∃ a,IsGLB S a

def WeakeningSuprema : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (τ : Ty) (P Q : World I) (h : Extends P Q),SupPreserving (τ := τ) h

def WeakeningInfima : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (τ : Ty) (P Q : World I) (h : Extends P Q),InfPreserving (τ := τ) h

/-- Literal finite ranked signature; no equality algorithm remains as a premise. -/
def FiniteSignatureEffectivity : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (I : Input (Fin n) arity) (τ : Ty) (P : World I),
    CompleteAt I τ P ∧ ∀ a : Value I τ P,a ∈ enumerateValues I τ P

end LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveNaturalLatticesTargets
