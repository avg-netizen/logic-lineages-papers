module

public import LogicLineages.OrdinalComparison.SourceApplicativeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets

def ApplicativeAssignmentEquations : Prop :=
  (∀ (Γ : List Ty) (τ : Ty) (t : OriginalTerm Γ τ) (v : OrdinalVector Γ τ.level),
    ordinalCanonicalPrime t = some v → ordinalApplicativeAssignment t = some v) ∧
  (∀ (Γ : List Ty) (σ τ : Ty) (f : OriginalTerm Γ (.arrow σ τ)) (a : OriginalTerm Γ σ),
    ordinalApplicativeAssignment (.app f a) = do
      let vf ← ordinalApplicativeAssignment f
      let va ← ordinalApplicativeAssignment a
      pure (ordinalCanonicalApplication vf va)) ∧
  (∀ (Γ : List Ty) (σ τ : Ty) (body : OriginalTerm (σ :: Γ) τ),
    ordinalApplicativeAssignment (.lam body) = none)

def ApplicativeAssignmentDomain : Prop :=
  ∀ (Γ : List Ty) (τ : Ty) (t : OriginalTerm Γ τ),
    (∃ v, ordinalApplicativeAssignment t = some v) ↔ applicativeOnly t = true

def ApplicativeAssignmentGrade : Prop :=
  ∀ (Γ : List Ty) (τ : Ty) (t : OriginalTerm Γ τ) (v : OrdinalVector Γ τ.level),
    ordinalApplicativeAssignment t = some v → ∀ i, GeneratedOrdinalGrade Γ i.val (v i)

def SuccessorProbeAssignment : Prop :=
  ∀ (Γ : List Ty) (v : Variable Γ .ground),
    ordinalApplicativeAssignment (successorProbe v) =
      some (fun _ => .collapse .one (.add .one (.var ⟨.ground, v, 0⟩)))

end LogicLineages.OrdinalComparison.Source.Targets
