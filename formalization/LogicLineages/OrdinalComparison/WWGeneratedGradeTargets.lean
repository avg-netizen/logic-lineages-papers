module
public import LogicLineages.OrdinalComparison.WWGeneratedGradeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets

def ActualGeneratedGradeRenaming : Prop :=
  ∀ (Γ Δ : List Ty) (ρ : Renaming Γ Δ) (i : Nat) (t : OrdinalExpression Γ),
    GeneratedOrdinalGrade Γ i t →
      GeneratedOrdinalGrade Δ i (ordinalExpressionRename ρ t)

def ActualGeneratedGradeHeadClosure : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    GeneratedOrdinalGrade (σ :: Γ) i t →
      GeneratedOrdinalGrade Γ i (ordinalHeadClosure t)

def ActualGeneratedGradePartial : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    GeneratedOrdinalGrade (σ :: Γ) i t → ∃ v : OrdinalPartialVector Γ σ,
      ordinalTypedPartial i t = some v ∧ ∀ j, GeneratedOrdinalGrade Γ j.val (v j)

end LogicLineages.OrdinalComparison.Source.Targets
