module
public import LogicLineages.OrdinalComparison.KernelInputProgramDefinitions
public import LogicLineages.OrdinalComparison.ProfileThresholdProgramDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Faithful normal notation for the actual source principal omega^eta. -/
def comparisonPrincipalNote (eta : NONote) : NONote := by
  letI := eta.2
  exact ⟨ONote.oadd eta.1 1 0,inferInstance⟩

def encodedComparisonPrincipalNote (eta : Nat) : Nat := Nat.pair eta 0+1

/-- Requested-profile-dependent source separation modulus, paying both
original profile thresholds and the actual same-principal mass classifier. -/
def encodedLimitPairCertificateTail (eta P c e : Nat) : Nat :=
  max (encodedProfileSupplierTail (encodedComparisonPrincipalNote eta) P)
    (encodedPrincipalKernelMassModulus eta c e)

end LogicLineages.OrdinalComparison
