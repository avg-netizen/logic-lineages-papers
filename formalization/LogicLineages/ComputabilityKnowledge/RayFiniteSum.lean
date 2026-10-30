module

public import LogicLineages.ComputabilityKnowledge.RayDominance
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.NatAbs

@[expose] public section

/-! The actual finite lower-key sum in the source ray estimate N3.
Integer slopes/constants are the coefficients after subtracting two maps.
No eventual ordering of the actual hereditary keys is supplied here.
-/
namespace LogicLineages.ComputabilityKnowledge.RayFiniteSum

def coefficientMass {ι : Type*} (s : Finset ι) (A C : ι → Int) : Nat :=
  ∑ i ∈ s, ((A i).natAbs + (C i).natAbs)

def lowerSum {ι : Type*} (s : Finset ι) (A C : ι → Int)
    (exponent : ι → Nat) (t : Nat) : Int :=
  ∑ i ∈ s, (A i * (t : Int) + C i) * ((2 ^ exponent i : Nat) : Int)

end LogicLineages.ComputabilityKnowledge.RayFiniteSum
