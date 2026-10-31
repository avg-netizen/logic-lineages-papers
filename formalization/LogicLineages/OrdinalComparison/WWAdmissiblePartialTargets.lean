module
public import LogicLineages.OrdinalComparison.WWAdmissiblePartialDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open AdmissibleSum AdmissiblePartial
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- All structural policies, not only L/R: every generated graded input has a
successful graded literal partial. This is not the ambient C_i norm domain. -/
def ActualAdmissiblePartialGenerated : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (p : Policy) (i : Nat)
    (t : OrdinalExpression (σ :: Γ)),
    GeneratedOrdinalGrade (σ :: Γ) i t →
    ∃ v, run p i t = some v ∧ ∀ j, GeneratedOrdinalGrade Γ j.val (v j)

/-- Same literal input under any two structural policies: success and actual
ordinal values agree. No claim about whole-source policy independence. -/
def ActualAdmissiblePartialValue : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (p q : Policy) (i : Nat)
    (t : OrdinalExpression (σ :: Γ)) (v : OrdinalPartialVector Γ σ),
    run p i t = some v → ∃ w, run q i t = some w ∧
      ∀ (j : Fin (σ.level + 2)) (ρ : OrdinalComponent Γ → Ordinal),
        denote ρ (v j) = denote ρ (w j)

end LogicLineages.OrdinalComparison.Source.Targets
