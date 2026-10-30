module

public import LogicLineages.ComputabilityKnowledge.RayFamilyClosure
public import LogicLineages.ComputabilityKnowledge.RayHeightInduction
public import LogicLineages.ComputabilityKnowledge.RayCodeEvaluation

@[expose] public section

/-! Complete literal finite-family ray algorithm for paper02 lem:ray. Inputs
may have different height bounds. Close under original recursive keys and add
zeros, lift by the original structural embeddings, collect one common ray,
and compute every sign by evaluating the ORIGINAL codes at the common bound.
Sign 0 means equal, 1 means first smaller, 2 means first larger. -/
namespace LogicLineages.ComputabilityKnowledge.RaySeparation

open ExponentialNormalForm ExponentialHereditaryCodec
open RayFamilyClosure RayCoefficientCollection RayUniformBounds

def weights (d : Nat) (roots : List HeightCode) : List Nat :=
  sharedWeights d (maxHeight roots) (liftedFamily d roots)

def threshold (d : Nat) (roots : List HeightCode) : Nat :=
  commonThreshold d (maxHeight roots) (liftedFamily d roots)

def rayList (d : Nat) (roots : List HeightCode) (t : Nat) : List Nat :=
  (weights d roots).map (fun a => a * t)

def signCode (d : Nat) (roots : List HeightCode) (p q : HeightCode) : Nat :=
  let xs := rayList d roots (threshold d roots)
  let a := RayCodeEvaluation.evalCode d p.1 p.2 xs
  let b := RayCodeEvaluation.evalCode d q.1 q.2 xs
  if a = b then 0 else if a < b then 1 else 2

noncomputable def originalValue (d : Nat) (roots : List HeightCode) (p : HeightCode) (t : Nat) : Nat :=
  value p.1 (formDecode d p.1 p.2) (fun i => (weights d roots).getD i.val 0 * t)

end LogicLineages.ComputabilityKnowledge.RaySeparation
