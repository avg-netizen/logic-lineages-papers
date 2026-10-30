module
public import LogicLineages.OrdinalComparison.EncodedCompensatedCountDefinitions
public import LogicLineages.OrdinalComparison.EncodedNaturalSumDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Existing raw notation codec specialized to a natural ordinal. -/
def encodedNatNote (n : Nat) : Nat :=
  if n=0 then 0 else encodedNodeCode 0 (n-1) 0

/-- Literal principal plus finite-tail initial state. Source calibration assumes
a positive faithful exponent; every raw numeric input nevertheless has a value. -/
def encodedKernelInitial (n a t : Nat) : Nat :=
  encodedNodeCode n 0 (encodedNatNote (t-a-(1+rawNormCode n)))

noncomputable def encodedSuffixKernelCount (n a t : Nat) : Nat :=
  encodedCompensatedCountValue a (encodedKernelInitial n a t)

noncomputable def encodedSuffixKernelValue (n a t : Nat) : Nat :=
  (Phi^[encodedSuffixKernelCount n a t]) t

end LogicLineages.OrdinalComparison
