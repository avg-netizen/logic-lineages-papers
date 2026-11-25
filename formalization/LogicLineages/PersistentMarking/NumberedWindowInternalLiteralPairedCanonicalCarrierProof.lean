module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPairedAuxInstalledProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCanonicalScalarNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScalarReinstallThinProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPairedCanonicalCarrierProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs)
open NumberedWindowInternalLiteralCoveredMemo (coveredMemoWindow WindowSeedsCovered)
open NumberedWindowInternalLiteralCoveredTypedAuxCasesProof (ActiveRaw)
open NumberedWindowInternalLiteralPairedAuxInstalledProof (exact_ConcretePairedCoveredTypedAuxTuple)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (pairedExchange)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowInternalLiteralRoundLeastTargets (SameLeastOnEdge)
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

/-- Choose the paired exchange before reinstalling the scalar and
its positive application frontend. The carrier packet therefore uses
the same physical least as the proved edge coherence. -/
theorem exact_ConcretePairedCanonicalCarrierPacket (xs : Entries) (s : Settings) (W : List ProbeTy)
    (valid : ValidWindow s W) (seeds : WindowSeedsCovered s)
    (symmetric : HeadPairsSymmetric s.equivalentHeads) :
    ∃ (oldI cv tv : Program 1) (leaf : Nat → Program 3) (C other : Program 3) (directed base : Program 2)
      (T V : Program 1) (v : Inputs),
      let X := guardedExchange C s (pairedExchange directed)
      let win := coveredMemoWindow C s base T V
      let R := ActiveRaw C s leaf other base T V
      let L := packedLeastProgram C X win s
      let i := addressScalar cv tv win L
      NumberedWindowInternalLiteralCoveredTypedAuxInstalledProof.Packet xs s W oldI cv tv leaf C other X base T V v ∧
      Packet xs s W i cv tv R L (applicationCore L) (frontendInputs i L v) ∧
      SameLeastOnEdge C X win s := by
  obtain ⟨oldI,cv,tv,leaf,C,other,directed,base,T,V,v,orig,coherent⟩ :=
    exact_ConcretePairedCoveredTypedAuxTuple xs s W valid seeds symmetric
  let X := guardedExchange C s (pairedExchange directed)
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
  exact ⟨oldI,cv,tv,leaf,C,other,directed,base,T,V,v,orig,
    exact_ReinstallLiteralDirectCarrier xs s W valid i (jRaw oldI) cv tv d
      (applicationCore L) R L (frontendInputs i L v) fitted,coherent⟩


#print axioms exact_ConcretePairedCanonicalCarrierPacket
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPairedCanonicalCarrierProof
