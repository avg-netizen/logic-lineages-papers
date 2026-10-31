module
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open AdmissibleSum AdmissibleAssignment

def ActualAdmissibleAbstractionGenerated : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (m : Nat) (p : Policy)
    (h : OrdinalVector (σ :: Γ) m),
    (∀ i, GeneratedOrdinalGrade (σ :: Γ) i.val (h i)) →
    ∃ v, abstraction p h = some v ∧ ∀ j, GeneratedOrdinalGrade Γ j.val (v j)

/-- Full arbitrary structural-policy totality and generated grammar. This is
not original norm-admissibility, and no arbitrary selector is called computable. -/
def ActualAdmissibleAssignmentGenerated : Prop :=
  ∀ (Γ : List Ty) (τ : Ty) (p : Policy) (t : OriginalTerm Γ τ),
    ∃ v, assignment p t = some v ∧ ∀ j, GeneratedOrdinalGrade Γ j.val (v j)

/-- Positive closure for all actual typed sources whose free names are ground,
under any fixed structural source policy. Effective evaluation/scalar
translation remain separate obligations. -/
def ActualAdmissibleAssignmentPositiveClosed : Prop :=
  ∀ (Γ : List Ty), (∀ τ ∈ Γ, τ = Ty.ground) →
    ∀ (τ : Ty) (p : Policy) (t : OriginalTerm Γ τ),
    ∃ v, assignment p t = some v ∧
      ∀ j, 0 < j.val → ordinalExpressionVariables (v j) = []

end LogicLineages.OrdinalComparison.Source.Targets
