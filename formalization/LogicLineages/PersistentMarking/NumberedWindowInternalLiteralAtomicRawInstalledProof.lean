module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawShapeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPairedCanonicalCarrierProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScalarReinstallThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCanonicalScalarNumericProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawInstalledProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs)
open NumberedWindowInternalSparseTuple (InstalledTupleAt)
open NumberedWindowInternalSparseTypedRawInstallationChecks (exact_ReinstallCalibratedRawTuple)
open NumberedWindowInternalLiteralDirectCarrierInstalledProof
  (Packet exact_ReinstallLiteralDirectCarrier)
open NumberedWindowInternalLiteralAtomicRawGuardProof (guardedRaw exact_LiteralAtomicGuardedRaw)
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
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseApplicationFrontend (applicationCore)
open NumberedWindowInternalSparseApplicationReinstall (frontendInputs)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalLiteralCount (permutation)

/-- Select the calibrated raw atom gate in the actual installed body.
The target scalar gate and both direct rules are reconstructed there,
not moved from a body with an extensionally equal callback. -/
theorem exact_ReinstallLiteralAtomicRawPacket (xs : Entries) (s : Settings) (W : List ProbeTy)
    (valid : ValidWindow s W) (i j cv tv : Program 1) (d p₀ : Program 3)
    (raw : Program 5) (L : Program 3) (v : Inputs)
    (old : InstalledTupleAt xs s W i j cv tv d p₀ raw L v) :
    Packet xs s W i cv tv (guardedRaw raw) L p₀ v := by
  have fit := exact_LiteralAtomicGuardedRaw xs s raw old.2.2.1.2.2.1
  have newer := exact_ReinstallCalibratedRawTuple xs s W valid i j cv tv d p₀
    raw (guardedRaw raw) L v old fit
  exact exact_ReinstallLiteralDirectCarrier xs s W valid i j cv tv d p₀ (guardedRaw raw) L v newer

/-- Rebuild the actual paired, canonical-scalar Paper 16 packet with
the calibrated raw atom guard physically installed. The existing
cover, paired exchange, memo, least program, and scalar remain exact.
The raw atom facts are not yet claims about the least representatives
of a certificate's original addresses. -/
theorem exact_ConcretePairedCanonicalAtomicRawPacket (xs : Entries) (s : Settings) (W : List ProbeTy)
    (valid : ValidWindow s W) (seeds : WindowSeedsCovered s)
    (symmetric : HeadPairsSymmetric s.equivalentHeads) :
    ∃ (cv tv : Program 1) (leaf : Nat → Program 3) (C other : Program 3) (directed base : Program 2)
      (T V : Program 1) (v : Inputs),
      let X := guardedExchange C s (pairedExchange directed)
      let win := coveredMemoWindow C s base T V
      let raw := ActiveRaw C s leaf other base T V
      let L := packedLeastProgram C X win s
      let i := addressScalar cv tv win L
      Packet xs s W i cv tv (guardedRaw raw) L (applicationCore L) (frontendInputs i L v) ∧
        SameLeastOnEdge C X win s := by
  obtain ⟨oldI,cv,tv,leaf,C,other,directed,base,T,V,v,orig,coherent⟩ :=
    exact_ConcretePairedCoveredTypedAuxTuple xs s W valid seeds symmetric
  let X := guardedExchange C s (pairedExchange directed)
  let win := coveredMemoWindow C s base T V
  let raw := ActiveRaw C s leaf other base T V
  let L := packedLeastProgram C X win s
  let i := addressScalar cv tv win L
  let r := addressPositive cv tv raw L
  let d := dCore oldI r permutation
  have calls := orig.physical.2.2.1
  have cal := exact_LiteralAddressScalarCalibration s cv tv win L calls.1 calls.2.1 orig.windowFit orig.leastFit
  have chosen := (exact_ReinstallLiteralScalar xs s W valid i oldI (jRaw oldI) cv tv d
    (applicationCore L) raw L v cal orig.physical).2
  exact ⟨cv,tv,leaf,C,other,directed,base,T,V,v,
    exact_ReinstallLiteralAtomicRawPacket xs s W valid i (jRaw oldI) cv tv d
      (applicationCore L) raw L (frontendInputs i L v) chosen,coherent⟩

#print axioms exact_ReinstallLiteralAtomicRawPacket
#print axioms exact_ConcretePairedCanonicalAtomicRawPacket
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawInstalledProof
