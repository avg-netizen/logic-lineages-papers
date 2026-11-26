module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredCarrierReportsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredTypedAuxInstalledProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralResidualProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredCarrierInstallProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs)
open NumberedWindowInternalLiteralCoveredMemo (coveredMemoWindow WindowSeedsCovered)
open NumberedWindowInternalLiteralCoveredTypedAuxCasesProof (ActiveRaw)
open NumberedWindowInternalLiteralCoveredTypedAuxInstalledProof (Packet exact_ConcreteCoveredTypedAuxTuple)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseApplicationFrontend (applicationCore)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)

/-- At one covered selection, the carrier wrapper has the exact
covered raw checker as its underlying callback, and retains the same
selected least and application program. The original and wrapped
packets are both built afresh, with no transport between bodies. -/
theorem exact_CoveredCarrierPacket (xs : Entries) (s : Settings) (W : List ProbeTy)
    (valid : ValidWindow s W) (seeds : WindowSeedsCovered s) :
    ∃ (i cv tv : Program 1) (leaf : Nat → Program 3) (C other : Program 3) (X base : Program 2)
      (T V : Program 1) (v : Inputs),
      let R := ActiveRaw C s leaf other base T V
      let L := packedLeastProgram C X (coveredMemoWindow C s base T V) s
      Packet xs s W i cv tv leaf C other X base T V v ∧
      NumberedWindowInternalLiteralDirectCarrierInstalledProof.Packet
        xs s W i cv tv R L (applicationCore L) v := by
  obtain ⟨i,cv,tv,leaf,C,other,X,base,T,V,v,orig⟩ := exact_ConcreteCoveredTypedAuxTuple xs s W valid seeds
  let R := ActiveRaw C s leaf other base T V
  let L := packedLeastProgram C X (coveredMemoWindow C s base T V) s
  let d := dCore i (addressPositive cv tv R L) permutation
  exact ⟨i,cv,tv,leaf,C,other,X,base,T,V,v,orig,
    NumberedWindowInternalLiteralDirectCarrierInstalledProof.exact_ReinstallLiteralDirectCarrier
      xs s W valid i (jRaw i) cv tv d (applicationCore L) R L v orig.physical⟩

#print axioms exact_CoveredCarrierPacket
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredCarrierInstallProof
