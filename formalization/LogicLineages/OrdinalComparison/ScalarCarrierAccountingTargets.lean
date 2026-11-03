module
public import LogicLineages.OrdinalComparison.ScalarCarrierAccountingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ScalarCarrierAccounting.Targets
open ActiveScalarAnnotation AdditiveHeadTree OriginalDomain

def AccountingOrigin : Prop := ∀ (k : Nat) (Γ : List Ty)
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)) (xs : List Carrier) (c : Nat),
  Account q xs c → ∀ label ∈ xs, ∃ h t,
    SelectedAffineHead.SelectedCollapse
      (.here : Variable (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (k+1))) q h t ∧
    Ordinal.omega0 ≤ unitValue h ∧ label.head = unitValue h

/-- Actual run and literal accounting are derived from the independently
source-built certificates. Every carrier label contains actual source bytes,
whole assignment and ground-closure proof, not a free ordinal value. -/
def ExactAccounting : Prop := ∀ (k : Nat) (Γ : List Ty)
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)),
  ScalarTrees (.here : Variable (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (k+1))) q →
  Annotated OrdinalSyntax.defaultPolicy
    (.here : Variable (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (k+1))) q →
  ∃ (xs : List Carrier) (c : Nat) (v : OrdinalPartialVector Γ (Ty.curriedGround (k+1))),
    Account q xs c ∧ AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 q = some v ∧
    ∀ μ : Variable Γ .ground → Nat,
      expressionValue (UnitObservation.substitution μ) (v (HeadFiniteSurplus.outputOne k)) =
        carrierSum xs + (c : Ordinal)

/-- Full original-source instantiation with no supplied accounting, carrier,
assignment, partial-success, grade or annotation premise. Lower reserve and
transport identities remain separate obligations. -/
def ActualSourceAccounting : Prop := ∀ (k : Nat) (Γ : List Ty) (n : Nat)
    (e : TrackedSource.Expr k (Ty.curriedGround (k+1) :: Γ) .here n),
  ∃ (u : OrdinalVector (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround n).level)
    (xs : List Carrier) (c : Nat) (v : OrdinalPartialVector Γ (Ty.curriedGround (k+1))),
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase e) = some u ∧
    Account (u 0) xs c ∧ AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (u 0) = some v ∧
    ∀ μ : Variable Γ .ground → Nat,
      expressionValue (UnitObservation.substitution μ) (v (HeadFiniteSurplus.outputOne k)) =
        carrierSum xs + (c : Ordinal)
end LogicLineages.OrdinalComparison.Source.ScalarCarrierAccounting.Targets
