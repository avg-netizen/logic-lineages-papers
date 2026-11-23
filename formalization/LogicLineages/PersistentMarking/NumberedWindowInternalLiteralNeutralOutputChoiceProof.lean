module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralOutputChoiceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralPhysicalChoiceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalApplicationOutputGuardReinstallProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralOutputChoiceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseApplicationFrontendTargets (ActualScalarCalibration)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseApplicationReinstall (frontendInputs)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalAtomicApplicationShape (refinedApplication)
open NumberedWindowInternalApplicationOutputGuardTargets (outputGuard)
open NumberedWindowInternalApplicationOutputGuardReinstallTargets (selectOutputInputs OutputScalarLaw)
open NumberedWindowInternalApplicationOutputGuardReinstallProof (exact_ApplicationOutputGuardReselect)
open NumberedWindowInternalNeutralAuxiliaryLiteralBodyProof (neutralWithCarrier)
open NumberedWindowInternalAuxBottomMembership (augmented)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralNeutralPhysicalChoiceProof (exact_SelectedLiteralNeutralPhysicalScalar)
open NumberedWindowInternalLiteralNeutralOutputChoiceTargets

/-- Select one exact same-body p/h and retain all unrefined reports.
The output carrier supplier is entirely numeric and separate. -/
theorem exact_SelectedLiteralNeutralOutput :
    ∃ C : Program 3, ActualSelectedCoverOutput C ∧
      ∀ (xs : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
        (∀ i, ActualScalarCalibration s i → OutputScalarLaw s i) →
        SelectedNeutralOutputAt C xs s W := by
  obtain ⟨C,cover,choose⟩ := exact_SelectedLiteralNeutralPhysicalScalar
  refine ⟨C,cover,?_⟩
  intro xs s W valid ensure
  obtain ⟨cv,tv,V,X,root,other,windowProg,v,hroot,hother,hsyntax,hwindow,hX,
    callbacks,isc,keeps,guardEq,base,report,neutral,body,odd⟩ := choose xs s W valid
  let raw := typedRaw5 root other windowProg V
  let least := packedLeastProgram C X windowProg s
  let i := addressScalar cv tv windowProg least
  let R := addressPositive cv tv raw least
  let N := augmented i (neutralWithCarrier i R)
  let old := frontendInputs i least v
  have carrierLaw : OutputScalarLaw s i := ensure i isc
  obtain ⟨sameA,fresh⟩ := exact_ApplicationOutputGuardReselect xs s W valid i (jRaw i)
    N (dCore i N permutation) old carrierLaw neutral
  refine ⟨cv,tv,V,X,root,other,windowProg,v,hroot,hother,hsyntax,hwindow,hX,
    callbacks,isc,keeps,guardEq,base,report,neutral,body,odd,sameA.trans keeps,?_,fresh⟩
  change outputGuard i (refinedApplication old.applicationGuard) =
    outputGuard i (refinedApplication (applicationGuard i least))
  exact congrArg (fun p => outputGuard i (refinedApplication p)) guardEq

#print axioms exact_SelectedLiteralNeutralOutput
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralOutputChoiceProof
