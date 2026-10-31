module
public import LogicLineages.OrdinalComparison.WWOriginalBoundedDeltaDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OriginalDomain AdmissibleSum AdmissibleAssignment

/-- Actual typed application is the specified restriction of the source box;
its coordinate zero is retained, so the original supported bound persists. -/
def OriginalSourceApplicationBounded : Prop :=
  ∀ (Γ : List Ty) (σ τ : Ty) (p : Policy)
    (f : OrdinalVector Γ (Ty.arrow σ τ).level) (g : OrdinalVector Γ σ.level),
    (∀ j, AmbientGrade Γ j.val (f j)) →
    (∀ j, AmbientGrade Γ j.val (g j)) →
    SourceBoundedVector f → SourceBoundedVector g →
    (∀ j, AmbientGrade Γ j.val (application p f g j)) ∧
      SourceBoundedVector (application p f g)

/-- Every actual original-T zero-history source assignment, for every
structural macro policy, is total, lies in the original norm-admissible C
classes, and is bounded under exactly the occurring-variable substitutions.
No generated-grammar, norm-admissibility or output-bound hypothesis is assumed.
This does not assert reduction-history compatibility, decrease, or effective
scalar translation of the output ordinals. -/
def OriginalSourceAssignmentBounded : Prop :=
  ∀ (Γ : List Ty) (τ : Ty) (p : Policy) (t : OriginalTerm Γ τ),
    ∃ v : OrdinalVector Γ τ.level,
      assignment p t = some v ∧
      (∀ j, AmbientGrade Γ j.val (v j)) ∧ SourceBoundedVector v

end LogicLineages.OrdinalComparison.Source.Targets
