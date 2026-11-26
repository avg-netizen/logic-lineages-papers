module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSelectedChildWindowProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCanonicalScalarNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScalarReinstallThinProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCanonicalCarrierInstallProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs)
open NumberedWindowInternalLiteralCoveredMemo (coveredMemoWindow WindowSeedsCovered)
open NumberedWindowInternalLiteralCoveredTypedAuxCasesProof (ActiveRaw)
open NumberedWindowInternalLiteralCoveredTypedAuxInstalledProof (exact_ConcreteCoveredTypedAuxTuple)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseApplicationFrontend (applicationCore)
open NumberedWindowInternalSparseApplicationReinstall (frontendInputs)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalLiteralCanonicalScalarNumericProof (exact_LiteralAddressScalarCalibration)
open NumberedWindowInternalLiteralScalarReinstallThinProof (exact_ReinstallLiteralScalar)
open NumberedWindowInternalLiteralDirectCarrierInstalledProof (Packet exact_ReinstallLiteralDirectCarrier)

/-- The scalar callback is the genuine canonical coordinate checker
for the same covered window and least, in a concretely installed
original guard and direct step. No self-least fact is assumed to prove
numerical calibration or the existence of the installation. -/
theorem exact_CoveredCanonicalCarrierPacket (xs : Entries) (s : Settings) (W : List ProbeTy)
    (valid : ValidWindow s W) (seeds : WindowSeedsCovered s) :
    ∃ (oldI cv tv : Program 1) (leaf : Nat → Program 3) (C other : Program 3) (X base : Program 2)
      (T V : Program 1) (v : Inputs),
      let win := coveredMemoWindow C s base T V
      let R := ActiveRaw C s leaf other base T V
      let L := packedLeastProgram C X win s
      let i := addressScalar cv tv win L
      NumberedWindowInternalLiteralCoveredTypedAuxInstalledProof.Packet xs s W oldI cv tv leaf C other X base T V v ∧
      Packet xs s W i cv tv R L (applicationCore L) (frontendInputs i L v) := by
  obtain ⟨oldI,cv,tv,leaf,C,other,X,base,T,V,v,orig⟩ := exact_ConcreteCoveredTypedAuxTuple xs s W valid seeds
  let win := coveredMemoWindow C s base T V
  let R := ActiveRaw C s leaf other base T V
  let L := packedLeastProgram C X win s
  let i := addressScalar cv tv win L
  let r := addressPositive cv tv R L
  let d := dCore oldI r permutation
  have calls := orig.physical.2.2.1
  have cal := exact_LiteralAddressScalarCalibration s cv tv win L calls.1 calls.2.1 orig.windowFit orig.leastFit
  have fitted := (exact_ReinstallLiteralScalar xs s W valid i oldI (jRaw oldI) cv tv d
    (applicationCore L) R L v cal orig.physical).2
  exact ⟨oldI,cv,tv,leaf,C,other,X,base,T,V,v,orig,
    exact_ReinstallLiteralDirectCarrier xs s W valid i (jRaw oldI) cv tv d
      (applicationCore L) R L (frontendInputs i L v) fitted⟩

#print axioms exact_CoveredCanonicalCarrierPacket
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCanonicalCarrierInstallProof
