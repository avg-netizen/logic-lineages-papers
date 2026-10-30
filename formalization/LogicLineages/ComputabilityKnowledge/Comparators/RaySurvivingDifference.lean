module

public import LogicLineages.ComputabilityKnowledge.RaySurvivingDifference

@[expose] public section

/-! Literal source subtraction with zero affine coefficients discarded.
Well-formed, constant-free lower-height keys are derived from the original
maps' own WellFormed predicate, rather than supplied by a separate oracle.
-/
namespace LogicLineages.ComputabilityKnowledge.Comparators.RaySurvivingDifference

open ExponentialNormalForm RayMapDifference RayFiniteSum
open LogicLineages.ComputabilityKnowledge.RaySurvivingDifference

def ExactSurvivingSupport : Prop :=
  ∀ (d h : Nat) (f g : Form d (h + 1)) (key : Form d h),
    key ∈ survivingKeys f g ↔ key ∈ keySet f g ∧ f key ≠ g key

def NonemptySurvivingSupport : Prop :=
  ∀ (d h : Nat) (f g : Form d (h + 1)), (survivingKeys f g).Nonempty ↔ f ≠ g

def ActualSurvivingSum : Prop :=
  ∀ (d h : Nat) (f g : Form d (h + 1)) (weights : Fin d → Nat) (t : Nat),
    ((value (h + 1) f (fun i => weights i * t) : Nat) : Int) -
        ((value (h + 1) g (fun i => weights i * t) : Nat) : Int) =
      lowerSum (survivingKeys f g) (slopeDifference weights f g) (constantDifference f g)
        (fun key => value h key (fun i => weights i * t)) t

def ActualLowerKeys : Prop :=
  ∀ (d h : Nat) (f g : Form d (h + 1)), WellFormed (h + 1) f → WellFormed (h + 1) g →
    ∀ key ∈ survivingKeys f g, WellFormed h key ∧ constantCoefficient h key = 0

def Target : Prop := ExactSurvivingSupport ∧ NonemptySurvivingSupport ∧
  ActualSurvivingSum ∧ ActualLowerKeys

end LogicLineages.ComputabilityKnowledge.Comparators.RaySurvivingDifference
