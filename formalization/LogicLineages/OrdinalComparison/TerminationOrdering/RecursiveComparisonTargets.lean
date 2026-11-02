module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveComparisonDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveComparisonTargets
open Source Source.SourceMarkedSyntax RecursiveComparison

def WeakTypeSoundness : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ : List Ty) (s t : Packed Symbol arity Γ), Weak Symbol arity above Γ s t → s.1=t.1

def StrictTypeSoundness : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ : List Ty) (s t : Packed Symbol arity Γ), Strict Symbol arity above Γ s t → s.1=t.1

def MarkedStrictEmpty : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ : List Ty) (f : Head Symbol) (τ : Ty) (base : Arguments Symbol arity Γ (headArguments arity f))
    (types : List Ty) (extras : Arguments Symbol arity Γ types) (t : Packed Symbol arity Γ),
    ¬ Strict Symbol arity above Γ ⟨τ,.marked f τ base types extras⟩ t

def StrictMarkHelperAgreement : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty)
    (τ : Ty) (s r : MarkedTerm Symbol arity Γ τ), strictMark s=some r → markSpine s=some r

def StrictWeakInclusion : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ : List Ty) (s t : Packed Symbol arity Γ), Strict Symbol arity above Γ s t → Weak Symbol arity above Γ s t

def LiteralOrdinaryReflexivity : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ : List Ty) (τ : Ty) (s : Term Symbol arity Γ τ), Weak Symbol arity above Γ ⟨τ,embed s⟩ ⟨τ,embed s⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveComparisonTargets
