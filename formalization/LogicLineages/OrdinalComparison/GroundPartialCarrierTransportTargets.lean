module
public import LogicLineages.OrdinalComparison.GroundPartialCarrierTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundPartialCarrierTransport.Targets
open ActiveScalarAnnotation AdditiveHeadTree ScalarCarrierAccounting OriginalDomain

/-- Literal adjacent kernel calibration only. The public transport below has
arbitrary prefix depth, reduced through actual typed permutation/naturality. -/
def AdjacentClosureCalibration : Prop := ∀ (k : Nat) (Γ : List Ty)
    (q : OrdinalExpression (Ty.ground :: Ty.curriedGround (k+1) :: Γ)),
  GroundClosing.expression (GroundClosing.GroundMap.lift (GroundOperatorDischarge.groundMap Γ)) (before k [] Γ q) =
    ordinalHeadClosure q ∧
  (Active (.here : Variable (Ty.curriedGround (k+1) :: Ty.ground :: Γ) _) (before k [] Γ q) ↔
    Active (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) q) ∧
  HeadFiniteSurplus.surplus (ordinalHeadClosure q) = HeadFiniteSurplus.surplus (before k [] Γ q) ∧
  unitValue (ordinalHeadClosure q) = unitValue (before k [] Γ q)

/-- Actual ground scalar partial success is derived from the source-built
certificates. Same genuine occurrence labels and order, with nondecreasing
finite constant and therefore reserve. NO adjacent-only restriction. -/
def GroundPartialAccount : Prop := ∀ (k : Nat) (left right : List Ty)
    (q : OrdinalExpression ((Ty.ground :: left) ++ Ty.curriedGround (k+1) :: right))
    (xs : List Carrier) (c : Nat),
  ScalarTrees (SelectedBinder.selected (Ty.ground :: left) right (Ty.curriedGround (k+1))) q →
  Annotated OrdinalSyntax.defaultPolicy
    (SelectedBinder.selected (Ty.ground :: left) right (Ty.curriedGround (k+1))) q →
  Account (before k left right q) xs c →
  ∃ (v : OrdinalPartialVector (left ++ Ty.curriedGround (k+1) :: right) Ty.ground) (c' : Nat),
    AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 q = some v ∧
    Account (after k left right (v 0)) xs c' ∧ c ≤ c' ∧ reserve xs c ≤ reserve xs c'

/-- Unconditional original source transport at every nested binder position.
The original whole vector and actually permuted source vector are retained;
old and new selected-F partial identities are proved for the SAME actual
carrier list. The ground derivative scalar is not called a source term. -/
def ActualSourceGroundPartial : Prop := ∀ (k : Nat) (left right : List Ty) (n : Nat)
    (e : TrackedSource.Expr k ((Ty.ground :: left) ++ Ty.curriedGround (k+1) :: right)
      (SelectedBinder.selected (Ty.ground :: left) right (Ty.curriedGround (k+1))) n),
  ∃ (u : OrdinalVector ((Ty.ground :: left) ++ Ty.curriedGround (k+1) :: right) (Ty.curriedGround n).level)
    (xs : List Carrier) (c : Nat)
    (v : OrdinalPartialVector (left ++ Ty.curriedGround (k+1) :: right) Ty.ground) (c' : Nat)
    (oldPart : OrdinalPartialVector ((Ty.ground :: left) ++ right) (Ty.curriedGround (k+1)))
    (newPart : OrdinalPartialVector (left ++ right) (Ty.curriedGround (k+1))),
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase e) = some u ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy
      (SelectedAccountPreparation.prepareSource (Ty.ground :: left) right (Ty.curriedGround (k+1))
        (TrackedSource.erase e)) =
      some (SourceRenaming.renameVector
        (SelectedBinder.moveToHead (Ty.ground :: left) right (Ty.curriedGround (k+1))) u) ∧
    Account (before k left right (u 0)) xs c ∧
    AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (u 0) = some v ∧
    Account (after k left right (v 0)) xs c' ∧ c ≤ c' ∧ reserve xs c ≤ reserve xs c' ∧
    AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (before k left right (u 0)) = some oldPart ∧
    AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (after k left right (v 0)) = some newPart ∧
    ∀ (μold : Variable ((Ty.ground :: left) ++ right) Ty.ground → Nat)
      (μnew : Variable (left ++ right) Ty.ground → Nat),
      expressionValue (UnitObservation.substitution μold) (oldPart (HeadFiniteSurplus.outputOne k)) =
        carrierSum xs + (c : Ordinal) ∧
      expressionValue (UnitObservation.substitution μnew) (newPart (HeadFiniteSurplus.outputOne k)) =
        carrierSum xs + (c' : Ordinal)
end LogicLineages.OrdinalComparison.Source.GroundPartialCarrierTransport.Targets
