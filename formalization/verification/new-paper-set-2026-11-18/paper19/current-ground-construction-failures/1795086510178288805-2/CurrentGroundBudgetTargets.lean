module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundBudgetDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundBudgetTargets

open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent (PolicyShape)
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open CurrentGroundBudget OriginalSecondBudget HeadFiniteSurplus AdditiveHeadTree

/-- The actual source partial's second coordinate is finite at every
remaining valuation, not merely after a selected numerical assignment. -/
def ExactScalarSecond : Prop :=
  ∀ (p : AdmissibleSum.Policy) (k : Nat) (Γ : List Ty)
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)),
    ScalarTrees (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q →
    ∃ v : OrdinalPartialVector Γ (Ty.curriedGround (k+1)),
      AdmissiblePartial.run p 0 q = some v ∧ 1 ≤ scalarSecond q ∧
      ∀ (f : Nat → Nat) (ν : OrdinalComponent Γ → Ordinal),
        ParametricSourceSuccessor.denoteWith f ν (v (outputTwo k)) = (scalarSecond q : Ordinal)

/-- Independent generated-source floor, not deduced from integer reserve.
The selected repeat can be any actual ordered allowed shape. -/
def SourceSecondFloor : Prop :=
  ∀ (p : AdmissibleSum.Policy) (k : Nat) (Γ : List Ty) (n : Nat)
    (e : TrackedSource.Expr k (Ty.curriedGround (k+1) :: Γ) .here n),
    ∃ (u : OrdinalVector (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround n).level)
      (v : OrdinalPartialVector Γ (Ty.curriedGround (k+1))),
      AdmissibleAssignment.assignment p (TrackedSource.erase e) = some u ∧
      AdmissiblePartial.run p 0 (u 0) = some v ∧
      CurrentReserve.sourceFloor e ≤ (scalarSecond (u 0) : Int) ∧
      ∀ (f : Nat → Nat) (ν : OrdinalComponent Γ → Ordinal),
        ParametricSourceSuccessor.denoteWith f ν (v (outputTwo k)) = (scalarSecond (u 0) : Ordinal)

def OriginalBox : Prop :=
  ∀ (p : AdmissibleSum.Policy) (k : Nat) (Γ : List Ty)
    (P : TrackedSource.Expr k (Ty.curriedGround (k+1) :: Γ) .here 0)
    (C : OriginalTerm Γ (Ty.curriedGround (k+1))), TrackedSource.active P = true →
    ∃ (u : OrdinalVector (Ty.curriedGround (k+1) :: Γ) 0)
      (B : OrdinalVector Γ (Ty.arrow (Ty.curriedGround (k+1)) Ty.ground).level)
      (caller : OrdinalVector Γ (Ty.curriedGround (k+1)).level)
      (v : OrdinalPartialVector Γ (Ty.curriedGround (k+1))) (b : Nat),
      AdmissibleAssignment.assignment p (TrackedSource.erase P) = some u ∧
      AdmissibleAssignment.assignment p (.lam (TrackedSource.erase P)) = some B ∧
      AdmissibleAssignment.assignment p C = some caller ∧
      AdmissiblePartial.run p 0 (u 0) = some v ∧
      B (boxFirst k) = v (outputOne k) ∧ B (boxSecond k) = v (outputTwo k) ∧
      b = scalarSecond (u 0) ∧ 4 ≤ b ∧
      AdmissibleAssignment.box p B caller (boxSecond k) = B (boxSecond k) ∧
      (∀ (f : Nat → Nat) (ν : OrdinalComponent Γ → Ordinal),
        ParametricSourceSuccessor.denoteWith f ν (B (boxSecond k)) = (b : Ordinal)) ∧
      budgetCode p ((Ty.curriedGround (k+1) :: Γ).map SyntaxCode.typeCode)
        (SyntaxCode.encodeTerm (TrackedSource.erase P)) = some b

def BudgetEffective : Prop :=
  ∀ p : AdmissibleSum.Policy, PolicyShape.Effective p →
    Computable (fun z : List Nat × Nat => budgetCode p z.1 z.2)

def Full : Prop := ExactScalarSecond ∧ SourceSecondFloor ∧ OriginalBox ∧ BudgetEffective

end LogicLineages.ControlSensitivityCurrent.CurrentGroundBudgetTargets
