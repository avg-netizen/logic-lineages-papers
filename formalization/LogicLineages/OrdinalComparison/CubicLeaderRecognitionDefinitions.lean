module
public import LogicLineages.OrdinalComparison.CounterLeaderExpansionDefinitions
public import LogicLineages.OrdinalComparison.KernelInputProgramDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.CubicLeaderRecognition

/-- Literal existing encoded principal modulus specialized to exponent three. -/
def cubicModulus (c e : Nat) : Nat := max 16 (max c e + 4)

/-- Preserve every original higher entry domain as well as the cubic modulus. -/
def leaderTail (n c e : Nat) : Nat :=
  max (CounterLeaderExpansion.threshold n c) (cubicModulus (c+3) (e+3))

end LogicLineages.OrdinalComparison.CubicLeaderRecognition
