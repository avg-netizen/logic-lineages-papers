module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawInstalledProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScalarReinstallThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCanonicalScalarNumericProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastInstalledProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs)
open NumberedWindowInternalLiteralCoveredMemo (WindowSeedsCovered coveredMemoWindow)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (pairedExchange)
open NumberedWindowInternalLiteralRoundLeastTargets (SameLeastOnEdge)
open NumberedWindowInternalLiteralCoveredTypedAuxCasesProof (ActiveRaw)
open NumberedWindowInternalLiteralPairedAuxInstalledProof (exact_ConcretePairedCoveredTypedAuxTuple)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalLiteralCanonicalScalarNumericProof (exact_LiteralAddressScalarCalibration)
open NumberedWindowInternalLiteralScalarReinstallThinProof (exact_ReinstallLiteralScalar)
open NumberedWindowInternalSparseLeastInstallationChecks (exact_ReinstallCalibratedLeast)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseApplicationFrontend (applicationCore)
open NumberedWindowInternalSparseApplicationReinstall (frontendInputs)
open NumberedWindowInternalSparseApplicationReinstallChecks (exact_ReinstallGuardedApplicationTuple)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralDirectCarrierInstalledProof (Packet)
open NumberedWindowInternalLiteralAtomicRawGuardProof (guardedRaw)
open NumberedWindowInternalLiteralAtomicRawInstalledProof (exact_ReinstallLiteralAtomicRawPacket)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast exact_LiteralAtomicGuardedLeast)

/-- The actual selected least program is the guarded original least,
and the raw program is the guarded original typed raw. The canonical
scalar, guarded application, and direct proof rules are reconstructed
on this choice without using equivalence of installed bodies. The
retained comparison says what it did for the underlying packed least;
the open guard supplies that underlying call when needed. -/
theorem exact_ConcretePairedCanonicalAtomicLeastPacket (xs : Entries) (s : Settings) (W : List ProbeTy)
    (valid : ValidWindow s W) (seeds : WindowSeedsCovered s)
    (symmetric : HeadPairsSymmetric s.equivalentHeads) :
    ∃ (cv tv : Program 1) (leaf : Nat → Program 3) (C other : Program 3) (directed base : Program 2)
      (T V : Program 1) (placed : Inputs),
      let X := guardedExchange C s (pairedExchange directed)
      let win := coveredMemoWindow C s base T V
      let raw := ActiveRaw C s leaf other base T V
      let L := guardedLeast (packedLeastProgram C X win s)
      let i := addressScalar cv tv win L
      Packet xs s W i cv tv (guardedRaw raw) L (applicationCore L) placed ∧
        SameLeastOnEdge C X win s := by
  obtain ⟨oldI,cv,tv,leaf,C,other,directed,base,T,V,v,orig,coherent⟩ :=
    exact_ConcretePairedCoveredTypedAuxTuple xs s W valid seeds symmetric
  let X := guardedExchange C s (pairedExchange directed)
  let win := coveredMemoWindow C s base T V
  let raw := ActiveRaw C s leaf other base T V
  let oldL := packedLeastProgram C X win s
  let L := guardedLeast oldL
  let i := addressScalar cv tv win L
  let r := addressPositive cv tv raw oldL
  let d := dCore oldI r permutation
  have hL := exact_LiteralAtomicGuardedLeast s oldL orig.leastFit
  have lifted := exact_ReinstallCalibratedLeast xs s W valid oldI (jRaw oldI) cv tv d (applicationCore oldL)
    raw oldL L v orig.physical hL
  let v₀ := frontendInputs oldI L v
  have app := (exact_ReinstallGuardedApplicationTuple xs s W valid oldI (jRaw oldI)
    cv tv d (applicationCore oldL) raw L v lifted).2
  have calls := orig.physical.2.2.1
  have cal := exact_LiteralAddressScalarCalibration s cv tv win L calls.1 calls.2.1 orig.windowFit hL
  have rebuilt := (exact_ReinstallLiteralScalar xs s W valid i oldI (jRaw oldI) cv tv d
    (applicationCore L) raw L v₀ cal app).2
  exact ⟨cv,tv,leaf,C,other,directed,base,T,V,frontendInputs i L v₀,
    exact_ReinstallLiteralAtomicRawPacket xs s W valid i (jRaw oldI) cv tv d (applicationCore L)
      raw L (frontendInputs i L v₀) rebuilt,coherent⟩

#print axioms exact_ConcretePairedCanonicalAtomicLeastPacket
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastInstalledProof
