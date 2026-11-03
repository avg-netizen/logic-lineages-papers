module
public import LogicLineages.OrdinalComparison.SelectedHeadCarrierDefinitions
public import LogicLineages.OrdinalComparison.HeadFiniteSurplusDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SelectedAffineHead
open ActiveScalarAnnotation AdditiveHeadTree OriginalDomain HeadFiniteSurplus

/-- The same literal active scalar selection, retaining the selected tail too.
This permits a clause about EACH actual corresponding tail, even when identical
heads occur more than once with different tails. Exact coverage is proved. -/
inductive SelectedCollapse {k Γ} (F : Variable Γ (Ty.curriedGround (k+1))) :
    OrdinalExpression Γ → OrdinalExpression Γ → OrdinalExpression Γ → Prop where
  | here {h t} (active : Active F (.collapse h t)) : SelectedCollapse F (.collapse h t) h t
  | addLeft {a b h t} (selected : SelectedCollapse F a h t) : SelectedCollapse F (.add a b) h t
  | addRight {a b h t} (selected : SelectedCollapse F b h t) : SelectedCollapse F (.add a b) h t
  | tail {g s h t} (selected : SelectedCollapse F s h t) : SelectedCollapse F (.collapse g s) h t

/-- Exact complete head clause, on a literal head rather than a presumed
tracked source operator: additive positive tree, actual partial, finite
surplus/count, and genuine common-unit observations of that head. -/
def HeadConclusion {k Γ} (p : AdmissibleSum.Policy)
    (h : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)) : Prop :=
  HeadTree (.here : Variable (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (k+1))) h ∧
  ∃ v : OrdinalPartialVector Γ (Ty.curriedGround (k+1)),
    AdmissiblePartial.run p 1 h = some v ∧
    0 < secondCount h ∧
    (surplus h = 0 ↔ h = .var ⟨_,.here,UnaryCarrier.headIndex k⟩) ∧
    ∀ (ρ : Variable (Ty.curriedGround (k+1) :: Γ) .ground → Nat)
      (μ : Variable Γ .ground → Nat),
      expressionValue (UnitObservation.substitution μ) (v (outputOne k)) =
        expressionValue (UnitObservation.substitution ρ) h + (surplus h : Ordinal) ∧
      expressionValue (UnitObservation.substitution μ) (v (outputTwo k)) = (secondCount h : Ordinal) ∧
      (Ordinal.omega0 ≤ expressionValue (UnitObservation.substitution ρ) h → 1 ≤ surplus h)
end LogicLineages.OrdinalComparison.Source.SelectedAffineHead
