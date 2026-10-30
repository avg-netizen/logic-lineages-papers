module

public import LogicLineages.ComputabilityKnowledge.RayUniformBounds

@[expose] public section

/-! Original-map semantics for the finite-family height induction in paper02
lem:ray. The ray and threshold are the explicit programs already defined by
coefficient collection and uniform bounds, not chosen from successful rays.
Numeric evaluation/sign-program effectivity remains a separate supplier. -/
namespace LogicLineages.ComputabilityKnowledge.RayHeightInduction

open ExponentialNormalForm RayCoefficientCollection RayUniformBounds

noncomputable def rayValue (d H : Nat) (ns : List Nat) (k : Nat)
    (f : Form d k) (t : Nat) : Nat := value k f (sharedRay d H ns t)

noncomputable def OrderedAfter (d H : Nat) (ns : List Nat) (k : Nat)
    (f g : Form d k) : Prop :=
  ∀ t, commonThreshold d H ns ≤ t →
    rayValue d H ns k f t < rayValue d H ns k g t ∧
    (constantCoefficient k f = 0 → constantCoefficient k g = 0 →
      rayValue d H ns k f t + t ≤ rayValue d H ns k g t)

end LogicLineages.ComputabilityKnowledge.RayHeightInduction
