module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveComparisonDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryTemplateGrafting
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding RecursiveComparison

def EnvironmentsWeak {Symbol : Type} {arity : Symbol → Nat} (above : Symbol → Symbol → Prop)
    {Γ Δ : List Ty} (env env' : MarkedSubstitution Symbol arity Γ Δ) : Prop :=
  ∀ {σ} (v : Variable Γ σ), Weak Symbol arity above Δ ⟨σ,env v⟩ ⟨σ,env' v⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryTemplateGrafting
