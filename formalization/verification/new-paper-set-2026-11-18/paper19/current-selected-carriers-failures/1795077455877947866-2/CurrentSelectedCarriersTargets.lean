module
public import LogicLineages.ControlSensitivityCurrent.CurrentSelectedCarriersDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentSelectedCarriersTargets

open LogicLineages.OrdinalComparison.Source
open SourceFreeOccurrences CurrentSelectedCarriers
open CurrentUnaryChain (commonUnits)

def ExactFreshRename : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (F : Variable Γ σ),
    renameTrackedAt F F = .here ∧
    ∀ (τ : Ty) (x : Variable Γ τ), (⟨τ,x⟩ : PackedVariable Γ) ≠ ⟨σ,F⟩ →
      renameTrackedAt F x = .there x

def GroundSaturation : Prop :=
  ∀ (p : AdmissibleSum.Policy) (Γ : List Ty) (r : Nat)
    (t : OriginalTerm Γ (Ty.curriedGround (r+1)))
    (u : OrdinalVector Γ (Ty.curriedGround (r+1)).level),
    AdmissibleAssignment.assignment p t = some u →
    ∃ v : OrdinalVector Γ 1,
      AdmissibleAssignment.assignment p (UnaryCarrier.saturate r t) = some v ∧
      v 1 = u (UnaryCarrier.headIndex r)

def GroundIndependence : Prop :=
  ∀ (f : Nat → Nat) (Γ : List Ty) (i : Nat) (e : OrdinalExpression Γ),
    0 < i → GeneratedOrdinalGrade Γ i e →
    ∀ (ρ μ : Variable Γ .ground → Nat),
      ParametricSourceSuccessor.denoteWith f (commonUnits μ)
        (GroundClosing.expression (UnaryCarrier.groundMap Γ) e) =
      ParametricSourceSuccessor.denoteWith f (commonUnits ρ) e

def ActualOperators : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat) (Γ : List Ty) (k r : Nat)
    (F : Variable Γ (Ty.curriedGround (k+1))) (t : OriginalTerm Γ (Ty.curriedGround (r+1))),
    ∃ (u : OrdinalVector Γ (Ty.curriedGround (r+1)).level)
      (w v : OrdinalVector (Ty.curriedGround (k+1) :: Γ) 1),
      Realization p f F r t u w v

def EverySelectedHead : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat) (k : Nat) (Γ : List Ty)
    (F : Variable Γ (Ty.curriedGround (k+1))) (n : Nat) (t : OriginalTerm Γ (Ty.curriedGround n)),
    @TrackedSource.Generated k Γ F n t →
    ∃ u : OrdinalVector Γ (Ty.curriedGround n).level,
      AdmissibleAssignment.assignment p t = some u ∧
      ∀ h, SelectedHeadCarrier.Selected F (u 0) h → HasSelectedCarrier p f F h

def Full : Prop := ExactFreshRename ∧ GroundSaturation ∧ GroundIndependence ∧ ActualOperators ∧ EverySelectedHead

end LogicLineages.ControlSensitivityCurrent.CurrentSelectedCarriersTargets
