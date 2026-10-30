module

public import LogicLineages.ComputabilityKnowledge.ExponentialHereditaryCodec
public import LogicLineages.ComputabilityKnowledge.AffineRayCalibration

@[expose] public section

/-! Paper02, lem:ray: collect the literal affine coefficients at every key
level before choosing one common ray. The semantic occurrence predicate is
independently defined on the original hereditary finite maps. The executable
collection traverses the existing natural-number codes, not semantic maps.
Canonicality is the previously proved normalizer's representation invariant;
no separation, calibration, or computability conclusion is assumed here.
-/
namespace LogicLineages.ComputabilityKnowledge.RayCoefficientCollection

open ExponentialNormalForm ExponentialNormalFormCodec ExponentialHereditaryCodec

noncomputable def CoefficientOccurs {d : Nat} :
    (h : Nat) → Form d h → Affine d → Prop
  | 0, f, a => a = f
  | h + 1, f, a => ∃ key ∈ f.support, a = f key ∨ CoefficientOccurs h key a

def coefficients : Nat → Nat → List CoeffCode
  | 0, n => [parseCoefficients n]
  | h + 1, n => (parseEntries n).flatMap (fun e => e.2 :: coefficients h e.1)

def collected (h : Nat) (ns : List Nat) : List CoeffCode :=
  [] :: ns.flatMap (coefficients h)

noncomputable def FamilyCoefficient (d h : Nat) (ns : List Nat) (a : Affine d) : Prop :=
  a = 0 ∨ ∃ n ∈ ns, CoefficientOccurs h (formDecode d h n) a

def sharedWeights (d h : Nat) (ns : List Nat) : List Nat :=
  AffineRayCalibration.weights d (collected h ns)

def sharedCutoff (h : Nat) (ns : List Nat) : Nat :=
  AffineRayCalibration.cutoff (collected h ns)

def sharedRay (d h : Nat) (ns : List Nat) (t : Nat) : Fin d → Nat :=
  AffineRayCalibration.rayTuple d (collected h ns) t

end LogicLineages.ComputabilityKnowledge.RayCoefficientCollection
