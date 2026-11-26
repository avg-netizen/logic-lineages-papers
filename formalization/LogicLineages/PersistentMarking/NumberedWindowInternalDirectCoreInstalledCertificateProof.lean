module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreInstalledCertificateTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreSharedTapeChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreInstalledCertificateProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.SourcePresentation (sourceBody)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectCoreSharedTapeChecks (exact_OpenOriginalDirectCoreSharedTape)
open NumberedWindowInternalDirectSourcePartitionRawTargets (sourceTape)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalDirectCoreInstalledCertificateTargets

theorem exact_InstalledCertificateSharedTape : ExactInstalledCertificateSharedTape := by
  intro i j r count c α Γ src w dst goal
  dsimp only
  intro cert next
  let D := dCore i r count
  let S := data i j r D
  let B := sourceBody S c
  have raw : Nonempty (Derivation B Γ (programGraph D (suc z) (sourceTape src w dst))) :=
    (exact_CertificateRules i j r D true c B α Γ src dst w).1 cert
  exact exact_OpenOriginalDirectCoreSharedTape i r count B α Γ src w dst goal raw next

#print axioms exact_InstalledCertificateSharedTape
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreInstalledCertificateProof
