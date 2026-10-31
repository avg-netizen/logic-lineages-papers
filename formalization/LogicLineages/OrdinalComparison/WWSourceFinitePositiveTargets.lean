module
public import LogicLineages.OrdinalComparison.WWSourceFinitePositiveDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open SourceClasses AdmissibleSum AdmissibleAssignment
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def FinitePositiveValueSound : Prop :=
  ∀ (Γ : List Ty) (t : OrdinalExpression Γ) (n : Nat),
    finitePositiveValue t = some n → 0 < n ∧
      ∀ ρ : OrdinalComponent Γ → Ordinal, denote ρ t = (n : Ordinal)

def GeneratedNoOmegaFinitePositive : Prop :=
  ∀ (Γ : List Ty) (i : Nat) (t : OrdinalExpression Γ),
    GeneratedOrdinalGrade Γ i t → 0 < i →
    ordinalExpressionVariables t = [] → noOmega t = true →
      ∃ n, finitePositiveValue t = some n

/-- First clause of cor:source-classes with the exact contextual ground-name
restriction; arbitrary internal binders/types and structural policies remain. -/
def ActualRecursorFreePositiveFinite : Prop :=
  ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
    ∀ (τ : Ty) (p : Policy) (t : OriginalTerm Γ τ), recursorFree t = true →
      ∃ v : OrdinalVector Γ τ.level, assignment p t = some v ∧
        ∀ j : Fin (τ.level + 1), 0 < j.val →
          ∃ n : Nat, 0 < n ∧ finitePositiveValue (v j) = some n ∧
            ∀ ρ : OrdinalComponent Γ → Ordinal, denote ρ (v j) = (n : Ordinal)
end LogicLineages.OrdinalComparison.Source.Targets
