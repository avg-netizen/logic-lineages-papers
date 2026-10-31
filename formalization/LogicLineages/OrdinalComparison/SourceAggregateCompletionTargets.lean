module
public import LogicLineages.OrdinalComparison.SourceAggregateCompletionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceAggregateCompletion.Targets
open OriginalDomain

/-- Whole paper09 lem:aggregate: the displayed explicit source construction
handles every finite conjunction, including empty lists, at every shared
original admissible or supported valuation. Functional free names and source
internals are unrestricted. No detector correctness premise is assumed.
This is not the later Boolean compiler's polynomial-DAG theorem. -/
def FullSourceAggregate : Prop :=
  (∀ (Γ : List Ty) (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground))
    (ρ : AdmissibleSubstitution Γ), AggregateAt (valuation ρ) es) ∧
  (∀ (Γ : List Ty) (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground))
    (S : VariableName Γ → Prop) (ρ : SupportedSubstitution Γ S),
    AggregateAt (supportedValuation ρ) es)
end LogicLineages.OrdinalComparison.Source.SourceAggregateCompletion.Targets
