module
public import LogicLineages.OrdinalComparison.SelectedHeadCarrierDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SelectedHeadCarrier.Targets

def SelectedActivity : Prop := ∀ (k : Nat) (Γ : List Ty)
    (F : Variable Γ (Ty.curriedGround (k+1))) (q h : OrdinalExpression Γ),
  Selected F q h → ActiveScalarAnnotation.Active F q

/-- Every selected head is backed by an actual original operator. The only
premise here is the independently constructed scalar certificate, not a list
of supplied operators or a presumed annotation-to-source correspondence. -/
def OperatorExtraction : Prop := ∀ (k : Nat) (Γ : List Ty)
    (F : Variable Γ (Ty.curriedGround (k+1))) (p : AdmissibleSum.Policy)
    (q h : OrdinalExpression Γ),
  ActiveScalarAnnotation.Annotated p F q → Selected F q h →
    GroundOperatorDischarge.OperatorWitness p h

/-- Full original tracked-source bridge: no assignment, annotation or operator
premise. It covers every selected head (therefore in particular every selected
nonfinite head). The exact actual scalar survives literal carrier construction. -/
def ActualSelectedCarriers : Prop := ∀ (k : Nat) (Γ : List Ty) (n : Nat)
    (e : TrackedSource.Expr k (Ty.curriedGround (k+1) :: Γ) .here n),
  ∃ u : OrdinalVector (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround n).level,
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase e) = some u ∧
    ∀ h, Selected (.here : Variable (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (k+1)))
      (u 0) h → HasActualCarrier h
end LogicLineages.OrdinalComparison.Source.SelectedHeadCarrier.Targets
