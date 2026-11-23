module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSparsePhysicalReinstallProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressThinDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressLiteralThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarInstallationThinProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPhysicalScalarReinstallProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenA)
open NumberedWindowInternalSparseTuple (InstalledTupleAt InstalledReportAt)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)
open NumberedWindowInternalSparseApplicationReinstall (frontendInputs)
open NumberedWindowInternalSparseApplicationFrontend (applicationCore)
open NumberedWindowInternalSparseApplicationFrontendTargets (ActualScalarCalibration)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalSparseCanonicalAddressLiteralThinProof (calibration)
open NumberedWindowInternalSparseScalarInstallationThinProof (reinstall)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalAtomicRefinement (refined)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralSparsePhysicalReinstallProof (reinstallPhysical)
open NumberedWindowGuardedGraphTargets (guard)

/-- The scalar can also be physically selected, rather than opaque:
use the exact original address tests and the same packed window and
least program present in the typed application and positive programs.
Rebuild the applications/probes and literal odd body for this exact
choice; no previous derivation is treated as a new-body derivation. -/
theorem exact_ReinstallLiteralPhysicalScalar
    (xs : Entries) (s : Settings) (W : List ProbeTy) (valid : ValidWindow s W)
    (oldI j cv tv : Program 1) (d oldCore windowProg : Program 3)
    (raw : Program 5) (least : Program 3) (v : Inputs)
    (window : ActualPackedWindow s windowProg)
    (prior : InstalledTupleAt xs s W oldI j cv tv d oldCore raw least v) :
    let i := addressScalar cv tv windowProg least
    let R := addressPositive cv tv raw least
    let RR := refined i R
    let updated := frontendInputs i least v
    ActualScalarCalibration s i ∧
      chosenA updated = chosenA v ∧ updated.applicationGuard = guard i (applicationCore least) ∧
      TupleAt xs s W i (jRaw i) R (dCore i R permutation) updated ∧
      InstalledReportAt i (jRaw i) cv tv (dCore i R permutation) raw least ∧
      TupleAt xs s W i (jRaw i) RR (dCore i RR permutation) updated := by
  let i := addressScalar cv tv windowProg least
  have cb := prior.2.2.1
  have isc : ActualScalarCalibration s i :=
    calibration s cv tv windowProg least cb.1 cb.2.1 window cb.2.2.2.1
  have first := reinstall xs s W valid i oldI j cv tv d oldCore raw least v isc prior
  let updated := frontendInputs i least v
  have second := reinstallPhysical xs s W valid.2.1 i j cv tv d (applicationCore least)
    raw least updated first.2
  exact ⟨isc,first.1,first.2.2.1,second⟩

#print axioms exact_ReinstallLiteralPhysicalScalar
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPhysicalScalarReinstallProof
