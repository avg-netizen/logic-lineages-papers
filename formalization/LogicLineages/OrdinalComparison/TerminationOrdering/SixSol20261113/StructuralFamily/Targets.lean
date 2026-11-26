module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.Targets
open CoherentConstructorLattice
/-- The proposed concrete family really satisfies every original family condition. -/
def ConcreteFamilyCoherent : Prop := Good familyRaw
/-- Failure is witnessed by the explicit family, not an unspecified weakening
of the generic source-family contract. -/
def ConcreteScannerFailure : Prop :=
  ∃ M : Constructors input, M.val = familyRaw ∧ ¬ ScannerSubstitutionAt M
/-- No assertion is made against the already checked fixed-point law. -/
def GenericScannerFailure : Prop := ¬ ∀ M : Constructors input, ScannerSubstitutionAt M
end LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.Targets
