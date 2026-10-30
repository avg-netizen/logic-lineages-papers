module
public import LogicLineages.OrdinalComparison.PositiveFiniteZerosDefinitions
public import LogicLineages.OrdinalComparison.PositiveNormalFlagDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- The actual source P1 countervaluation has unit weight and input Phi(k)+1,
with k the already computed finite-zero modulus. -/
noncomputable def encodedPositiveCounterInput (n m : Nat) : Nat :=
  Phi (encodedPositiveZeroBound n m)+1

end LogicLineages.OrdinalComparison
