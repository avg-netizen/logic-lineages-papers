module
public import LogicLineages.OrdinalComparison.WWOriginalBoundedDeltaDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OriginalDomain AdmissibleSum AdmissibleAssignment

/-- Actual variable assignment: universally bounded closed B substitutions pay
exactly the variable vector's original norm side condition. -/
def OriginalVariableAssignmentBounded : Prop :=
  ∀ (Γ : List Ty) (τ : Ty) (p : Policy) (x : Variable Γ τ),
    ∃ v : OrdinalVector Γ τ.level,
      assignment p (.var x) = some v ∧
      (∀ j, AmbientGrade Γ j.val (v j)) ∧ SourceBoundedVector v

/-- The common One vector used by Zero, successor and case constants. -/
def OriginalOneVectorBounded : Prop :=
  ∀ (Γ : List Ty) (m : Nat),
    (∀ j : Fin (m + 1), AmbientGrade Γ j.val (.one : OrdinalExpression Γ)) ∧
    SourceBoundedVector (fun _ : Fin (m + 1) => (.one : OrdinalExpression Γ))

/-- Actual recursor constant assignment with scalar Two and a single Omega
coordinate, under every ordered expansion policy. This is not the application
or whole-assignment F1 theorem. -/
def OriginalRecursorAssignmentBounded : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (p : Policy),
    ∃ v : OrdinalVector Γ (Ty.recType σ).level,
      assignment p (.recC σ) = some v ∧
      (∀ j, AmbientGrade Γ j.val (v j)) ∧ SourceBoundedVector v

end LogicLineages.OrdinalComparison.Source.Targets
