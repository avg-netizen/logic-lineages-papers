module
public import LogicLineages.OrdinalComparison.WWOriginalDomainDefinitions
public import LogicLineages.OrdinalComparison.WWGeneratedGradeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OriginalDomain

/-- Whole-free original C expressions satisfy the original head-sensitive
C^X promotion condition, without changing their norm premises. -/
def OriginalFreeAmbientHead : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    AmbientGrade (σ :: Γ) i t → ordinalHeadFree t = true → HeadGrade Γ σ i t

/-- The already independently proved source-generated grammar excludes
unsafe scalar promotions. Together with genuine original ambient C-validity
it supplies original C^X membership for lambda induction. Neither premise is
claimed for arbitrary ambient expressions; actual assignment outputs must
supply both separately. -/
def OriginalGeneratedAmbientHead : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    GeneratedOrdinalGrade (σ :: Γ) i t → AmbientGrade (σ :: Γ) i t → HeadGrade Γ σ i t

end LogicLineages.OrdinalComparison.Source.Targets
