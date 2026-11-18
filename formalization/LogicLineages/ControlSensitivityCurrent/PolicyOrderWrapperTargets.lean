module
public import LogicLineages.ControlSensitivityCurrent.FullAdditionTargets
public import LogicLineages.ControlSensitivityCurrent.PolicyCollisionDefinitions
public import LogicLineages.OrdinalComparison.SourceGroundEquivalenceDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyOrderWrapperTargets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open PolicyCollision
/-- Actual arbitrary-argument I application, not atomic-only/default-policy calibration. -/
def Identity : Prop := ∀ (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
  ∀ (p : AdmissibleSum.Policy) (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat)
    (t : OriginalTerm Γ .ground),
    rawScalar p f ρ (.app GroundEquivalence.identity t) = g f (rawScalar p f ρ t + 3)
/-- Actual arbitrary-argument K application, at the very same shared valuation. -/
def Constant : Prop := ∀ (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
  ∀ (p : AdmissibleSum.Policy) (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat)
    (t : OriginalTerm Γ .ground),
    rawScalar p f ρ (.app GroundEquivalence.constant t) = g f (rawScalar p f ρ t + 5)
/-- Literal composite eraser magnification, including actual raw zero=1. -/
def Magnify : Prop := ∀ (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
  ∀ (p : AdmissibleSum.Policy) (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat)
    (t : OriginalTerm Γ .ground),
    rawScalar p f ρ (GroundEquivalence.magnify t) = g f (3*rawScalar p f ρ t + 3)
/-- Genuine selected-policy/control strict-to-weak conversion; no functional-ordinal claim. -/
def OrderConversion : Prop := ∀ (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
  ∀ (p : AdmissibleSum.Policy) (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat)
    (a b : OriginalTerm Γ .ground),
    rawScalar p f ρ (GroundEquivalence.upper a) ≤ rawScalar p f ρ (GroundEquivalence.lower b) ↔
      rawScalar p f ρ a < rawScalar p f ρ b
end LogicLineages.ControlSensitivityCurrent.PolicyOrderWrapperTargets
