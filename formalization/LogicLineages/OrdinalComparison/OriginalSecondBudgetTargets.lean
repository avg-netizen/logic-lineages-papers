module
public import LogicLineages.OrdinalComparison.OriginalSecondBudgetDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalSecondBudget.Targets
open AdditiveHeadTree SourceReserveLowerBound
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- Actual successful partial is derived from the graded scalar certificate;
the second field is the exact finite count at EVERY remaining valuation. -/
def ExactScalarSecond : Prop := ∀ (k : Nat) (Γ : List Ty)
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)),
  ScalarTrees (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q →
  ∃ v : OrdinalPartialVector Γ (Ty.curriedGround (k+1)),
    AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 q = some v ∧
    1 ≤ scalarSecond q ∧
    ∀ ν : OrdinalComponent Γ → Ordinal,
      denote ν (v (HeadFiniteSurplus.outputTwo k)) = (scalarSecond q : Ordinal)

/-- Separate output-two source proof, not an inference from integer reserve.
All complete source assignments and partial successes are derived. -/
def ActualSourceSecond : Prop := ∀ (k : Nat) (Γ : List Ty) (n : Nat)
    (e : TrackedSource.Expr k (Ty.curriedGround (k+1) :: Γ) .here n),
  ∃ (u : OrdinalVector (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround n).level)
    (v : OrdinalPartialVector Γ (Ty.curriedGround (k+1))),
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase e) = some u ∧
    AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (u 0) = some v ∧
    sourceFloor e ≤ (scalarSecond (u 0) : Int) ∧
    ∀ ν : OrdinalComponent Γ → Ordinal,
      denote ν (v (HeadFiniteSurplus.outputTwo k)) = (scalarSecond (u 0) : Ordinal)

/-- Original B=lambda F.P and original actual caller in the old context.
The full box retains coordinate two literally; its actual finite budget is at
least four. No K, changed scale, or child-construction certificate is assumed. -/
def OriginalFullBoxBudget : Prop := ∀ (k : Nat) (Γ : List Ty)
    (P : TrackedSource.Expr k (Ty.curriedGround (k+1) :: Γ) .here 0)
    (C : OriginalTerm Γ (Ty.curriedGround (k+1))), TrackedSource.active P = true →
  ∃ (u : OrdinalVector (Ty.curriedGround (k+1) :: Γ) 0)
    (B : OrdinalVector Γ (Ty.arrow (Ty.curriedGround (k+1)) Ty.ground).level)
    (caller : OrdinalVector Γ (Ty.curriedGround (k+1)).level) (b : Nat),
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase P) = some u ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (.lam (TrackedSource.erase P)) = some B ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy C = some caller ∧
    b = scalarSecond (u 0) ∧ 4 ≤ b ∧
    AdmissibleAssignment.box OrdinalSyntax.defaultPolicy B caller (boxSecond k) = B (boxSecond k) ∧
    ∀ ν : OrdinalComponent Γ → Ordinal, denote ν (B (boxSecond k)) = (b : Ordinal)
end LogicLineages.OrdinalComparison.Source.OriginalSecondBudget.Targets
