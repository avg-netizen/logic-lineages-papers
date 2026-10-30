module
public import LogicLineages.OrdinalComparison.WWGeneratedSupportDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets

def ActualGeneratedComponentIndex : Prop :=
  ∀ (Γ : List Ty) (i : Nat) (t : OrdinalExpression Γ), GeneratedOrdinalGrade Γ i t →
    ∀ c ∈ ordinalExpressionVariables t, i ≤ c.2.2.val

def ActualGeneratedHeadFreeAbove : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    GeneratedOrdinalGrade (σ :: Γ) i t → σ.level < i → ordinalHeadFree t = true

def ActualGeneratedGroundPositiveClosed : Prop :=
  ∀ (Γ : List Ty), (∀ τ ∈ Γ, τ = Ty.ground) →
    ∀ (i : Nat) (t : OrdinalExpression Γ), 0 < i → GeneratedOrdinalGrade Γ i t →
      ordinalExpressionVariables t = []

end LogicLineages.OrdinalComparison.Source.Targets
