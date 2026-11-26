module
public import LogicLineages.ControlSensitivityCurrent.CurrentAffineHeadsDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentAffineHeadsTargets

open LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open CurrentAffineHeads AdditiveHeadTree ActiveScalarAnnotation
open CurrentUnaryChain (commonUnits)
open SelectedAffineHead (SelectedCollapse)

def PositiveNoCollapse : Prop :=
  ∀ (Γ : List Ty) (i : Nat) (e : OrdinalExpression Γ),
    0 < i → GeneratedOrdinalGrade Γ i e →
    collapseFree e = true ∧
    ∀ (f : Nat → Nat) (ν : OrdinalComponent Γ → Ordinal),
      ParametricSourceSuccessor.denoteWith f ν e = denote ν e

def SameCommonUnits : Prop :=
  ∀ (Γ : List Ty) (ρ : Variable Γ .ground → Nat),
    OriginalDomain.valuation (UnitObservation.substitution ρ) = commonUnits ρ

def ActualHead : Prop :=
  ∀ (k : Nat) (Γ : List Ty) (p : AdmissibleSum.Policy) (f : Nat → Nat)
    (h : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)),
    HeadTree (.here : Variable (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (k+1))) h →
    HeadConclusion p f h

def CompleteSource : Prop :=
  ∀ (k : Nat) (Γ : List Ty) (n : Nat) (p : AdmissibleSum.Policy) (f : Nat → Nat)
    (t : OriginalTerm (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround n)),
    @TrackedSource.Generated k (Ty.curriedGround (k+1) :: Γ) .here n t →
    ∃ u : OrdinalVector (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround n).level,
      AdmissibleAssignment.assignment p t = some u ∧
      (∀ j, 0 < j.val → HeadConclusion p f (u j)) ∧
      ∀ h s, SelectedCollapse (.here : Variable (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (k+1)))
        (u 0) h s → HeadConclusion p f h ∧
        (Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (k+1))) h →
          Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (k+1))) s)

def Full : Prop := PositiveNoCollapse ∧ SameCommonUnits ∧ ActualHead ∧ CompleteSource

end LogicLineages.ControlSensitivityCurrent.CurrentAffineHeadsTargets
