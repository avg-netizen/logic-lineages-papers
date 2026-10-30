module

public import LogicLineages.ComputabilityKnowledge.ExponentialNormalForm
public import LogicLineages.ComputabilityKnowledge.RayFiniteSum

@[expose] public section

/-! Literal finite-map subtraction on a positive ray. This is an algebraic
bridge to the checked N3 finite-sum estimate, not a separation oracle.
-/
namespace LogicLineages.ComputabilityKnowledge.RayMapDifference

open ExponentialNormalForm

noncomputable section

def raySlope {d : Nat} (weights : Fin d → Nat) (a : Affine d) : Nat :=
  ∑ i : Fin d, a i.succ * weights i

def keySet {d h : Nat} (f g : Form d (h + 1)) : Finset (Form d h) := by
  classical
  exact f.support ∪ g.support

def slopeDifference {d h : Nat} (weights : Fin d → Nat) (f g : Form d (h + 1))
    (key : Form d h) : Int :=
  (raySlope weights (f key) : Int) - raySlope weights (g key)

def constantDifference {d h : Nat} (f g : Form d (h + 1)) (key : Form d h) : Int :=
  (f key 0 : Int) - g key 0

end

end LogicLineages.ComputabilityKnowledge.RayMapDifference
