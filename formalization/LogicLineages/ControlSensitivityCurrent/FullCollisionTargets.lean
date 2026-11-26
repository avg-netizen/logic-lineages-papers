module
public import LogicLineages.ControlSensitivityCurrent.PolicyCollisionDefinitions
public import LogicLineages.ControlSensitivityCurrent.FullAdditionTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.FullCollision.Targets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open PolicyCollision
/-- Generic source-derived numerical supplier, no assumed supergrowth oracle. -/
def NumericCollision : Prop := ∀ f : Nat → Nat, FullAddition.Targets.SourceGrowth f →
  (∀ n : Nat, 0 < g f n ∧ 4*g f n < g f (n+1)) ∧
  ∀ x y : Nat, rightValue f x y ≤ leftValue f x y ∧
    (leftValue f x y = rightValue f x y ↔ x = y) ∧
    (x ≠ y → 2 ≤ leftValue f x y - rightValue f x y)
/-- Full current lem:collision, actual arbitrary ground sources at one joint valuation. -/
def CompleteCollision : Prop := ∀ f : Nat → Nat, FullAddition.Targets.SourceGrowth f →
  ∀ (p : AdmissibleSum.Policy) (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat),
  (∀ t : OriginalTerm Γ .ground, 0 < rawScalar p f ρ t ∧
    CompositeEraser.Scalar p f (fun c => ((ρ c+1 : Nat) : Ordinal)) t (rawScalar p f ρ t)) ∧
  ∀ a b : OriginalTerm Γ .ground,
    rawScalar p f ρ (SourceCollisionCompletion.detectorLeft a b) =
      leftValue f (rawScalar p f ρ a) (rawScalar p f ρ b) ∧
    rawScalar p f ρ (SourceCollisionCompletion.detectorRight a b) =
      rightValue f (rawScalar p f ρ a) (rawScalar p f ρ b) ∧
    rawScalar p f ρ (SourceCollisionCompletion.detectorRight a b) ≤
      rawScalar p f ρ (SourceCollisionCompletion.detectorLeft a b) ∧
    (rawScalar p f ρ (SourceCollisionCompletion.detectorLeft a b) =
      rawScalar p f ρ (SourceCollisionCompletion.detectorRight a b) ↔
      rawScalar p f ρ a = rawScalar p f ρ b) ∧
    (rawScalar p f ρ a ≠ rawScalar p f ρ b → 2 ≤
      rawScalar p f ρ (SourceCollisionCompletion.detectorLeft a b) -
      rawScalar p f ρ (SourceCollisionCompletion.detectorRight a b))
end LogicLineages.ControlSensitivityCurrent.FullCollision.Targets
