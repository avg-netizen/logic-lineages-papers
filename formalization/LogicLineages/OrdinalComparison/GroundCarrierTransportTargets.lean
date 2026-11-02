module
public import LogicLineages.OrdinalComparison.GroundCarrierTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundCarrierTransport.Targets
open ScalarCarrierAccounting ActiveScalarAnnotation OriginalDomain

/-- All-one observation only, not arbitrary scalar ground observations.
Source zero maps to ordinal one, so this equality must be proved literally. -/
def ExactUnitValue : Prop := ∀ (Γ Δ : List Ty) (r : GroundClosing.GroundMap Γ Δ)
    (q : OrdinalExpression Γ), unitValue (GroundClosing.expression r q) = unitValue q

def TrackedInvariants : Prop := ∀ (k : Nat) (Γ Δ : List Ty) (r : GroundClosing.GroundMap Γ Δ)
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)),
  ordinalHeadFree (GroundClosing.expression r.lift q) = ordinalHeadFree q ∧
  (Active (.here : Variable (Ty.curriedGround (k+1) :: Δ) _)
      (GroundClosing.expression r.lift q) ↔
    Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q) ∧
  HeadFiniteSurplus.surplus (GroundClosing.expression r.lift q) = HeadFiniteSurplus.surplus q

/-- EXACT same actual source labels, occurrence list, and finite constant.
Since reserve is c-3*length, its equality follows without a new assumption. -/
def ExactAccountTransport : Prop := ∀ (k : Nat) (Γ Δ : List Ty) (r : GroundClosing.GroundMap Γ Δ)
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)) (xs : List Carrier) (c : Nat),
  Account q xs c → Account (GroundClosing.expression r.lift q) xs c

/-- Unconditional complete source transport. Full vector (including scalar)
is the actual expression-map vector, NOT an unchanged arbitrary scalar value.
The actual scalar partial is transported by the actual map; the SAME literal
accounting and actual carrier labels give its positive common-unit identity. -/
def ActualSourceGroundTransport : Prop := ∀ (k : Nat) (Γ Δ : List Ty) (n : Nat)
    (r : GroundClosing.GroundMap Γ Δ)
    (e : TrackedSource.Expr k (Ty.curriedGround (k+1) :: Γ) .here n),
  ∃ (u : OrdinalVector (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround n).level)
    (xs : List Carrier) (c : Nat)
    (v : OrdinalPartialVector Γ (Ty.curriedGround (k+1)))
    (w : OrdinalPartialVector Δ (Ty.curriedGround (k+1))),
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase e) = some u ∧
    Account (u 0) xs c ∧ AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (u 0) = some v ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (close r (TrackedSource.erase e)) =
      some (GroundClosing.vector r.lift u) ∧
    Account (GroundClosing.expression r.lift (u 0)) xs c ∧
    AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (GroundClosing.expression r.lift (u 0)) = some w ∧
    w = GroundClosing.partialVector r v ∧
    ∀ μ : Variable Δ .ground → Nat,
      expressionValue (UnitObservation.substitution μ) (w (HeadFiniteSurplus.outputOne k)) =
        carrierSum xs + (c : Ordinal)
end LogicLineages.OrdinalComparison.Source.GroundCarrierTransport.Targets
