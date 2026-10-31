module
public import LogicLineages.OrdinalComparison.WWSourceClassesDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open SourceClasses AdmissibleSum AdmissibleAssignment

/-- Literal recursor-free sources introduce no literal Omega anywhere in their
actual assignment. Semantic finiteness additionally needs the contextual
closed-positive generated grammar; it is not claimed for free functional inputs. -/
def ActualRecursorFreeAssignmentNoOmega : Prop :=
  ∀ (Γ : List Ty) (τ : Ty) (p : Policy) (t : OriginalTerm Γ τ), recursorFree t = true →
    ∃ v, assignment p t = some v ∧ ∀ j, noOmega (v j) = true

/-- Every internal type and subtype in the exact existing source support is
bounded, not merely the result type. This independent source condition pays
the graded height bound of every actual assignment coordinate. -/
def ActualInternalLevelAssignmentHeight : Prop :=
  ∀ (Γ : List Ty) (τ : Ty) (p : Policy) (L : Nat) (t : OriginalTerm Γ τ),
    InternalLevelBound L t →
      ∃ v, assignment p t = some v ∧ ∀ j, headHeight (v j) ≤ L - j.val

end LogicLineages.OrdinalComparison.Source.Targets
