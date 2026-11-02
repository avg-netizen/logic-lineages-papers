module
public import LogicLineages.OrdinalComparison.SelectedAffineHeadDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SelectedAffineHead.Targets
open ActiveScalarAnnotation AdditiveHeadTree

def ExactSelectionCoverage : Prop := ∀ (k : Nat) (Γ : List Ty)
    (F : Variable Γ (Ty.curriedGround (k+1))) (q h : OrdinalExpression Γ),
  SelectedHeadCarrier.Selected F q h ↔ ∃ t, SelectedCollapse F q h t

/-- Both actual scalar certificates are consumed, so this conclusion never
infers head additivity from an arbitrary original operator witness. Every
selected tail is treated, not just some tail sharing a selected head value. -/
def SelectedTreeSupport : Prop := ∀ (k : Nat) (Γ : List Ty)
    (F : Variable Γ (Ty.curriedGround (k+1))) (p : AdmissibleSum.Policy)
    (q h t : OrdinalExpression Γ),
  ScalarTrees F q → Annotated p F q → SelectedCollapse F q h t →
    HeadTree F h ∧ (Active F h → Active F t)

/-- Full source-level affine-head assembly: the entire actual vector exists,
all positive source fields have the complete head conclusion, and EVERY
selected active scalar collapse head has that conclusion together with its
own tail-support implication. No certificates/operators/partial successes
are assumptions. Original source grammar and all shared names are retained. -/
def CompleteSourceAffineHeads : Prop := ∀ (k : Nat) (Γ : List Ty) (n : Nat)
    (p : AdmissibleSum.Policy)
    (e : TrackedSource.Expr k (Ty.curriedGround (k+1) :: Γ) .here n),
  ∃ u : OrdinalVector (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround n).level,
    AdmissibleAssignment.assignment p (TrackedSource.erase e) = some u ∧
    (∀ j, 0 < j.val → HeadConclusion p (u j)) ∧
    ∀ h t, SelectedCollapse (.here : Variable (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (k+1)))
      (u 0) h t → HeadConclusion p h ∧
      (Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (k+1))) h →
        Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (k+1))) t)
end LogicLineages.OrdinalComparison.Source.SelectedAffineHead.Targets
