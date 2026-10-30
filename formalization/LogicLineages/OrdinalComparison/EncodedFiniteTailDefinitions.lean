module
public import LogicLineages.OrdinalComparison.EncodedSuffixKernelDefinitions
public import LogicLineages.OrdinalComparison.FiniteTail

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Finite-right CNF addition using the existing numerical natural-sum merge.
Its agreement with ordinary ordinal finite-tail addition is separately proved. -/
def encodedFiniteTail (h n : Nat) : Nat := encodedNaturalSum h (encodedNatNote n)

end LogicLineages.OrdinalComparison
