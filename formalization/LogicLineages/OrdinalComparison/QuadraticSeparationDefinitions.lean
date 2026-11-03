module
public import LogicLineages.OrdinalComparison.FiniteKernelRecursionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.QuadraticSeparation

/-- The literal signed exponent in source equation V, before totalization. -/
def signedDepth (j : Int) (w : Nat) : Int := (Phi w / 2 : Nat) + j + 1

/-- Exactly the numerical premise in the degree-two uniform separation proof. -/
def Region (w : Nat) (j k : Int) (R : Nat) : Prop :=
  j.natAbs + k.natAbs + R + 4 ≤ Phi w / 2

end LogicLineages.OrdinalComparison.QuadraticSeparation
