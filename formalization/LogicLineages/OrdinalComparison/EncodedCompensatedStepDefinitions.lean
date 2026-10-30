module
public import LogicLineages.OrdinalComparison.EncodedDescentDefinitions
public import LogicLineages.OrdinalComparison.SuffixKernelDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Literal numeric controlled descent with permanent numerical mass c.
Finite codes are absorbing; normal nonfinite codes use the existing exact
encoded maximum and additive norm. No ordinal evaluation occurs here. -/
def encodedCompensatedStep (c n : Nat) : Nat :=
  if encodedFiniteTest n then n
  else encodedMaximumPredecessor (rawSplitCode n).unpair.1 (Phi (c+rawNormCode n)-c)

end LogicLineages.OrdinalComparison
