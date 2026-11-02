module
public import LogicLineages.OrdinalComparison.SourceReserveLowerBoundDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceReserveLowerBound.Targets
open ScalarCarrierAccounting
/-- Actual positive generated heads under the common all-one observation. -/
def PositiveHeadValue : Prop := ∀ (Γ : List Ty) (i : Nat) (h : OrdinalExpression Γ),
  0 < i → GeneratedOrdinalGrade Γ i h → (1 : Ordinal) ≤ unitValue h

/-- Every literal Account, under every injective typed change of context which
sends the actual tracked name to here. Original assignment success is explicit;
the unconditional source theorem below discharges it. -/
def RenamedSourceLowerBound : Prop := ∀ (k : Nat) (Γ Δ : List Ty)
    (F : Variable Γ (Ty.curriedGround (k+1))) (n : Nat)
    (e : TrackedSource.Expr k Γ F n)
    (u : OrdinalVector Γ (Ty.curriedGround n).level)
    (r : Renaming Γ (Ty.curriedGround (k+1) :: Δ)),
  (∀ τ, Function.Injective (fun x : Variable Γ τ => r x)) → r F = .here →
  AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase e) = some u →
  ∀ (xs : List Carrier) (c : Nat), Account (ordinalExpressionRename r (u 0)) xs c →
    sourceFloor e ≤ reserve xs c

/-- Original complete source vector and a nonempty family of actual-carrier
accounts, all satisfying the source bound. No lower-bound or existence premise. -/
def ActualSourceLowerBound : Prop := ∀ (k : Nat) (Γ : List Ty) (n : Nat)
    (e : TrackedSource.Expr k (Ty.curriedGround (k+1) :: Γ) .here n),
  ∃ (u : OrdinalVector (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround n).level),
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase e) = some u ∧
    (∃ (xs : List Carrier) (c : Nat), Account (u 0) xs c) ∧
    ∀ (xs : List Carrier) (c : Nat), Account (u 0) xs c → sourceFloor e ≤ reserve xs c
end LogicLineages.OrdinalComparison.Source.SourceReserveLowerBound.Targets
