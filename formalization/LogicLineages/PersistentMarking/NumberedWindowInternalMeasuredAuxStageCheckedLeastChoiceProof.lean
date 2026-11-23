module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredAuxStagePhysicalReinstallProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeastDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRankAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeastNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRankProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredAuxStageCheckedLeastChoiceProof

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenA chosenH)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax ActualPackedWindow)
open NumberedWindowInternalSparseRawTickTargets (ActualRoot ActualFallback)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalSparseApplicationReinstall (frontendInputs)
open NumberedWindowInternalSparseApplicationFrontend (applicationCore)
open NumberedWindowInternalSparseApplicationFrontendTargets (ActualScalarCalibration)
open NumberedWindowInternalSparseTuple (CallbacksAt InstalledReportAt)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowGuardedGraphTargets (guard)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated GrammarOptionCalibrated factoredCover)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntax)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (TypeSyntaxCalibrated)
open NumberedWindowInternalCoverGrammarStageTargets (stageGenerator LayerPartsCalibrated)
open NumberedWindowInternalAuxWindowStepTargets (intrinsicQuery windowUpdate)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (measuredFactoredExchange)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (WindowSeedsCovered window)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowNeutralSpineRankProgramProof (exact_OriginalRawNeutralRankProgram)
open NumberedWindowInternalRankCheckedLeast (checkedLeast)
open NumberedWindowInternalRankCheckedLeastNumericProof (exact_OriginalRankCheckedLeastNumeric)
open NumberedWindowInternalSparseLeastInstallationChecks (exact_ReinstallCalibratedLeast)
open NumberedWindowInternalLiteralPhysicalScalarReinstallProof (exact_ReinstallLiteralPhysicalScalar)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration)
open NumberedWindowInternalSparseTuple (InstalledTupleAt)
open NumberedWindowInternalAtomicRefinement (refined)

/-- One measured original C/Xm/Wp, with a numerically conservative checked
least inserted at the same physical scalar, application and path programs.
Only the base numeric callback fits leave the previous proof body. -/
theorem selected :
    ∃ (g V TV baseM : Program 1) (P : Program 2) (nonAux : Program 5) (nextArgs : Program 2),
      let Va := auxSyntax V TV
      let G := stageGenerator nonAux nextArgs
      let M := selectedMeasure (measureUpdate baseM P)
      let C := factoredCover Va M G
      (∀ n, evaluate g (n ::ᵥ nil) = rawRank n) ∧
      ActualRawSyntax V ∧ TypeSyntaxCalibrated TV ∧ ActualRawSyntax Va ∧
      TermMeasureCalibrated M ∧ LayerPartsCalibrated nonAux nextArgs ∧
      GrammarOptionCalibrated G ∧ ActualSelectedCoverOutput C ∧
      ∀ (entries : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
        HeadPairsSymmetric s.equivalentHeads → WindowSeedsCovered s →
        ∃ (cv tv : Program 1) (base primitiveW : Program 2) (T : Program 1)
          (root other : Program 3) (v : Inputs),
          let baseW := intrinsicQuery (selectedIntrinsic (windowUpdate primitiveW T))
          let Wp := window C s baseW Va
          let Xm := measuredFactoredExchange s base Va baseM P G
          let raw := typedRaw5 root other Wp Va
          let baseL := packedLeastProgram C Xm Wp s
          let L := checkedLeast g baseL
          let i := addressScalar cv tv Wp L
          let R := addressPositive cv tv raw L
          let updated := frontendInputs i L v
          let RR := refined i R
          ActualRoot (NumberedWindowConcreteCheckers.root entries s) root ∧ ActualFallback other ∧
          ActualTermExchange s base ∧ ActualTermExchange s Xm ∧
          ActualPackedWindow s baseW ∧ ActualPackedWindow s Wp ∧
          ActualLeastCalibration s baseL ∧ ActualLeastCalibration s L ∧
          CallbacksAt entries s cv tv raw L ∧ ActualScalarCalibration s i ∧
          chosenA updated = chosenA v ∧ updated.applicationGuard = guard i (applicationCore L) ∧
          TupleAt entries s W i (jRaw i) R (dCore i R permutation) updated ∧
          InstalledReportAt i (jRaw i) cv tv (dCore i R permutation) raw L ∧
          TupleAt entries s W i (jRaw i) RR (dCore i RR permutation) updated := by
  obtain ⟨g,rankFit⟩ := exact_OriginalRawNeutralRankProgram
  obtain ⟨V,TV,baseM,P,nonAux,nextArgs,hV,hTV,hVa,hM,hParts,hGrammar,hC,pick⟩ := NumberedWindowInternalMeasuredAuxStagePhysicalReinstallProof.selected
  let Va := auxSyntax V TV
  let G := stageGenerator nonAux nextArgs
  let C := factoredCover Va (selectedMeasure (measureUpdate baseM P)) G
  refine ⟨g,V,TV,baseM,P,nonAux,nextArgs,rankFit,hV,hTV,hVa,hM,hParts,hGrammar,hC,?_⟩
  intro entries s W valid symmetric covered
  obtain ⟨cv,tv,base,primitiveW,T,root,other,v,hroot,hother,hbase,hXm,hBaseW,hWp,
    callbacks,scalar,keeps,guardEq,baseTuple,baseReport,_⟩ :=
    pick entries s W valid symmetric covered
  let Wp := window C s (intrinsicQuery (selectedIntrinsic (windowUpdate primitiveW T))) Va
  let Xm := measuredFactoredExchange s base Va baseM P G
  let raw := typedRaw5 root other Wp Va
  let baseL := packedLeastProgram C Xm Wp s
  let L := checkedLeast g baseL
  let baseI := addressScalar cv tv Wp baseL
  let baseR := addressPositive cv tv raw baseL
  let baseD := dCore baseI baseR permutation
  let update := frontendInputs baseI baseL v
  have baseCal : ActualLeastCalibration s baseL := callbacks.2.2.2.1
  have leastCal : ActualLeastCalibration s L :=
    exact_OriginalRankCheckedLeastNumeric s g baseL rankFit baseCal
  have prior : InstalledTupleAt entries s W baseI (jRaw baseI) cv tv baseD
      (applicationCore baseL) raw baseL update :=
    ⟨baseTuple,guardEq,callbacks,baseReport⟩
  have physical := exact_ReinstallCalibratedLeast entries s W valid baseI (jRaw baseI)
    cv tv baseD (applicationCore baseL) raw baseL L update prior leastCal
  obtain ⟨newScalar,newKeeps,newGuard,newTuple,newReport,refinedTuple⟩ :=
    exact_ReinstallLiteralPhysicalScalar entries s W valid baseI (jRaw baseI)
      cv tv baseD (applicationCore baseL) Wp raw L update hWp physical
  -- The output records the same older input leaves. Its new guard does
  -- not use the older application guard field; use the held update itself.
  exact ⟨cv,tv,base,primitiveW,T,root,other,update,hroot,hother,hbase,hXm,hBaseW,hWp,
    baseCal,leastCal,physical.2.2.1,newScalar,newKeeps,newGuard,newTuple,newReport,refinedTuple⟩

#print axioms selected
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredAuxStageCheckedLeastChoiceProof
