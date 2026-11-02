module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryTemplateGraftingDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryTemplateGraftingTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open RecursiveComparison OrdinaryTemplateGrafting

def EnvironmentGrafting : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ Δ : List Ty) (τ : Ty) (A : Term Symbol arity Γ τ)
    (env env' : MarkedSubstitution Symbol arity Γ Δ), EnvironmentsWeak above env env' →
    Weak Symbol arity above Δ ⟨τ,substituteTerm (embed A) env⟩ ⟨τ,substituteTerm (embed A) env'⟩

def DistinguishedVariableGrafting : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ : List Ty) (σ τ : Ty) (A : Term Symbol arity (σ::Γ) τ) (p q : MarkedTerm Symbol arity Γ σ),
    Weak Symbol arity above Γ ⟨σ,p⟩ ⟨σ,q⟩ →
    Weak Symbol arity above Γ
      ⟨τ,substituteTerm (embed A) (extendEnvironment (fun v => .var v) p)⟩
      ⟨τ,substituteTerm (embed A) (extendEnvironment (fun v => .var v) q)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryTemplateGraftingTargets
