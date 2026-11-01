module
public import LogicLineages.OrdinalComparison.KernelMassProgramDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Literal source RR same-principal rule: compare the actual inner inputs
first; only at equal inputs inspect the reverse mass key. -/
def encodedPrincipalKernelInputCompare (eta c e t u : Nat) : Nat :=
  if t<u then 0 else if u<t then 2 else encodedPrincipalKernelMassCompare eta c e

end LogicLineages.OrdinalComparison
