module

public import LogicLineages.ComputabilityKnowledge.RayMapDifference

@[expose] public section

/-! Exact source finite-map difference before the leading-key induction.
The normal forms are the original hereditary Finsupp maps, not a new
semantic representation with the desired equality stipulated as a field.
-/
namespace LogicLineages.ComputabilityKnowledge.Comparators.RayMapDifference

open ExponentialNormalForm RayFiniteSum
open LogicLineages.ComputabilityKnowledge.RayMapDifference

def LiteralAffineRay : Prop :=
  ∀ (d : Nat) (weights : Fin d → Nat) (a : Affine d) (t : Nat),
    affineValue a (fun i => weights i * t) = a 0 + raySlope weights a * t

def ActualMapDifference : Prop :=
  ∀ (d h : Nat) (f g : Form d (h + 1)) (weights : Fin d → Nat) (t : Nat),
    ((value (h + 1) f (fun i => weights i * t) : Nat) : Int) -
        ((value (h + 1) g (fun i => weights i * t) : Nat) : Int) =
      lowerSum (keySet f g) (slopeDifference weights f g) (constantDifference f g)
        (fun key => value h key (fun i => weights i * t)) t

def NontrivialSupport : Prop :=
  ∀ (d h : Nat) (f g : Form d (h + 1)), f ≠ g →
    ∃ key ∈ keySet f g, f key ≠ g key

def EqualCoefficientVanishes : Prop :=
  ∀ (d h : Nat) (f g : Form d (h + 1)) (weights : Fin d → Nat) (key : Form d h),
    f key = g key → slopeDifference weights f g key = 0 ∧ constantDifference f g key = 0

def Target : Prop := LiteralAffineRay ∧ ActualMapDifference ∧ NontrivialSupport ∧
  EqualCoefficientVanishes

end LogicLineages.ComputabilityKnowledge.Comparators.RayMapDifference
