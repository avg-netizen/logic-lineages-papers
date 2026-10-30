module

public import LogicLineages.ComputabilityKnowledge.RayCoefficientCollection
public import LogicLineages.ComputabilityKnowledge.RayMapDifference

@[expose] public section

/-! Literal uniform bounds used in paper02 lem:ray, N3. Width is measured on
actual hereditary finite maps; code bounds are explicit finite-list programs.
These definitions neither select a greatest key nor assume eventual gaps. -/
namespace LogicLineages.ComputabilityKnowledge.RayUniformBounds

open ExponentialNormalForm ExponentialNormalFormCodec ExponentialHereditaryCodec
open RayCoefficientCollection

noncomputable def HereditaryWidth {d : Nat} : (h : Nat) → Form d h → Nat → Prop
  | 0, _, _ => True
  | h + 1, f, N => f.support.card ≤ N ∧ ∀ key ∈ f.support, HereditaryWidth h key N

noncomputable def Covered (d H : Nat) (ns : List Nat) (h : Nat) (f : Form d h) : Prop :=
  ∀ a, CoefficientOccurs h f a → FamilyCoefficient d H ns a

def widthBound (H : Nat) (ns : List Nat) : Nat := (collected H ns).length

def weightMass (d H : Nat) (ns : List Nat) : Nat :=
  (collected H ns).foldr (fun c acc =>
    c.getD 0 0 + AffineRayCalibration.slope d (collected H ns) c + acc) 0

def massBound (d H : Nat) (ns : List Nat) : Nat :=
  4 * widthBound H ns * weightMass d H ns

def commonThreshold (d H : Nat) (ns : List Nat) : Nat :=
  max (sharedCutoff H ns) (RayDominance.threshold (massBound d H ns))

noncomputable def affineSize (d H : Nat) (ns : List Nat) (a : Affine d) : Nat :=
  a 0 + RayMapDifference.raySlope (fun i => (sharedWeights d H ns).getD i.val 0) a

end LogicLineages.ComputabilityKnowledge.RayUniformBounds
