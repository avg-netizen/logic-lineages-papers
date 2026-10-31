module
public import LogicLineages.OrdinalComparison.WWOriginalBoundedDeltaDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OriginalDomain AdmissibleSum AdmissibleAssignment

/-- Literal optional-tail macro, including the absent n=0 role, has the
original scalar domain and exact additive norm under every ordered policy. -/
def OriginalBoxTailGradeAndNorm : Prop :=
  ∀ (Γ : List Ty) (p : Policy) (n : Nat) (f g : OrdinalExpression Γ),
    AmbientGrade Γ 0 f → AmbientGrade Γ 0 g →
    AmbientGrade Γ 0 (boxTail p n f g) ∧
    ∀ ρ : AdmissibleSubstitution Γ,
      actualOrdinalNorm (expressionValue ρ (boxTail p n f g)) =
        actualOrdinalNorm (expressionValue ρ f) + actualOrdinalNorm (expressionValue ρ g) + n

/-- Original Corollary 2.12 on the actual source box, with all original
collapse C-domain conditions and supported bounded-norm estimates paid.
This is not yet whole-assignment F1 or a binder-sensitive C^X theorem. -/
def OriginalSourceBoxBounded : Prop :=
  ∀ (Γ : List Ty) (m n : Nat), n < m → ∀ (p : Policy)
    (f : OrdinalVector Γ m) (g : OrdinalVector Γ n),
    (∀ j, AmbientGrade Γ j.val (f j)) →
    (∀ j, AmbientGrade Γ j.val (g j)) →
    SourceBoundedVector f → SourceBoundedVector g →
    (∀ j, AmbientGrade Γ j.val (box p f g j)) ∧ SourceBoundedVector (box p f g)

end LogicLineages.OrdinalComparison.Source.Targets
