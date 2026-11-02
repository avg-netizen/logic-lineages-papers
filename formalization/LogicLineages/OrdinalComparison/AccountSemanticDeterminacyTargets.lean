module
public import LogicLineages.OrdinalComparison.AccountSemanticDeterminacyDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AccountSemanticDeterminacy.Targets
open ScalarCarrierAccounting ActiveScalarAnnotation AdditiveHeadTree OriginalDomain

/-- Actual labels need not be syntactically equal. Literal accounting fixes
only their ordered head values, occurrence count, finite c and integer reserve. -/
def AccountingDeterminacy : Prop := ∀ (k : Nat) (Γ : List Ty)
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (xs ys : List Carrier) (c d : Nat),
  Account q xs c → Account q ys d →
    headValues xs = headValues ys ∧ c = d ∧ xs.length = ys.length ∧ reserve xs c = reserve ys d

/-- Soundness for EVERY literal Account, not just the one returned by an
existence proof. The actual run is explicit, and no equality of chosen actual
carrier labels is assumed or asserted. -/
def UniversalSoundness : Prop := ∀ (k : Nat) (Γ : List Ty)
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)) (xs : List Carrier) (c : Nat)
    (v : OrdinalPartialVector Γ (Ty.curriedGround (k+1))),
  ScalarTrees (.here : Variable (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (k+1))) q →
  Annotated OrdinalSyntax.defaultPolicy
    (.here : Variable (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (k+1))) q →
  Account q xs c → AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 q = some v →
    ∀ μ : Variable Γ .ground → Nat,
      expressionValue (UnitObservation.substitution μ) (v (HeadFiniteSurplus.outputOne k)) =
        carrierSum xs + (c : Ordinal)

/-- Unconditional actual source instance: one actual full vector and actual
partial, a nonempty family of literal accountings, and soundness for ALL its
members. No supplier or chosen-account-equals-arbitrary premise remains. -/
def ActualSourceSoundness : Prop := ∀ (k : Nat) (Γ : List Ty) (n : Nat)
    (e : TrackedSource.Expr k (Ty.curriedGround (k+1) :: Γ) .here n),
  ∃ (u : OrdinalVector (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround n).level)
    (v : OrdinalPartialVector Γ (Ty.curriedGround (k+1))),
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase e) = some u ∧
    AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (u 0) = some v ∧
    (∃ (xs : List Carrier) (c : Nat), Account (u 0) xs c) ∧
    ∀ (xs : List Carrier) (c : Nat), Account (u 0) xs c →
      ∀ μ : Variable Γ .ground → Nat,
        expressionValue (UnitObservation.substitution μ) (v (HeadFiniteSurplus.outputOne k)) =
          carrierSum xs + (c : Ordinal)
end LogicLineages.OrdinalComparison.Source.AccountSemanticDeterminacy.Targets
