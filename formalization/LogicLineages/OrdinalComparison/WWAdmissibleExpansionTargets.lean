module
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentDefinitions
public import LogicLineages.OrdinalComparison.WWLiteralSizeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open AdmissibleSum

/-- Exact all-policy coordinate expansion bound E(|u|)=6*3^|u| from repaired
Proposition wwsc:prop:finite, on every successful literal partial. -/
def ActualAdmissiblePartialExpansion : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (p : Policy) (i : Nat)
    (t : OrdinalExpression (σ :: Γ)) (v : OrdinalPartialVector Γ σ),
    AdmissiblePartial.run p i t = some v →
      ∀ j, ordinalLiteralNodes (v j) ≤ 6 * 3 ^ ordinalLiteralNodes t

/-- Exact repeat-node formula, including the source scalar-repeat site. -/
def ActualAdmissibleRepeatExpansion : Prop :=
  ∀ (Γ : List Ty) (p : Policy) (site : MacroSite) (k : Nat), 0 < k →
    ∀ t : OrdinalExpression Γ,
      ordinalLiteralNodes (AdmissibleAssignment.repeated p site k t) + 1 =
        k * (ordinalLiteralNodes t + 1)

/-- The literal downward box recurrence's exact node count. No collapse
values or huge control values are evaluated. -/
def ActualLiteralBoxExpansion : Prop :=
  ∀ (Γ : List Ty) (n : Nat) (f g : Nat → OrdinalExpression Γ) (i : Nat),
    1 ≤ i → i ≤ n →
    ordinalLiteralNodes (ordinalBoxPositive n f g i) =
      ordinalLiteralNodes (ordinalBoxPositive n f g (i + 1)) +
      ordinalLiteralNodes (f i) + ordinalLiteralNodes (g i) + 2

end LogicLineages.OrdinalComparison.Source.Targets
