module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredSelectedGrammarCheckedLeastChoiceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankPartitionedCompleteRankReinstallProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredSelectedGrammarCheckedLeastPartitionedRankChoiceProof

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
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure CombineCalibrated)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated GrammarOptionCalibrated factoredCover)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntax)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (TypeSyntaxCalibrated)
open NumberedWindowInternalCoverSelectedGrammarOptionTargets (selectedGrammarOption)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalAuxWindowStepTargets (intrinsicQuery windowUpdate)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (measuredFactoredExchange)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (WindowSeedsCovered window)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowInternalRankCheckedLeast (checkedLeast)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration)
open NumberedWindowInternalNeutralAddressRank (addressRank)
open NumberedWindowInternalRankPartitionedAddress (rankPartitionedAddress)
open NumberedWindowInternalRankUniversalCarrier (completeRankEven)
open NumberedWindowInternalNeutralRankApplicationReinstallTargets (selectRankInputs)
open NumberedWindowInternalNeutralRankGuard (rankApplication)
open NumberedWindowInternalOriginalRankedTupleProof (OriginalOutputScalar)
open NumberedWindowInternalProbeTargets (FreshVariablesComputable)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalRankPartitionedCompleteRankReinstallProof (reselectRankApplication)

/-- One true measured C/X/W and one checked least and rank program through the complete
rank-partitioned even body and its original ranked p/h/a selection.
The old address-positive report is deliberately kept only inside its
separately named original unranked body. -/
theorem selected :
    ∃ (g V TV baseM : Program 1),
      let Va := auxSyntax V TV
      let M := selectedMeasure (measureUpdate baseM chosenCombine)
      let C := factoredCover Va M selectedGrammarOption
      (∀ n, evaluate g (n ::ᵥ nil) = rawRank n) ∧
      ActualRawSyntax V ∧ TypeSyntaxCalibrated TV ∧ ActualRawSyntax Va ∧
      TermMeasureCalibrated baseM ∧ CombineCalibrated chosenCombine ∧
      TermMeasureCalibrated M ∧ GrammarOptionCalibrated selectedGrammarOption ∧ ActualSelectedCoverOutput C ∧
      ∀ (entries : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
        HeadPairsSymmetric s.equivalentHeads → WindowSeedsCovered s → OriginalOutputScalar s →
        ∃ (cv tv : Program 1) (base primitiveW : Program 2) (T : Program 1)
          (root other : Program 3) (v : Inputs),
          let baseW := intrinsicQuery (selectedIntrinsic (windowUpdate primitiveW T))
          let Wp := window C s baseW Va
          let Xm := measuredFactoredExchange s base Va baseM chosenCombine selectedGrammarOption
          let raw := typedRaw5 root other Wp Va
          let baseL := packedLeastProgram C Xm Wp s
          let L := checkedLeast g baseL
          let i := addressScalar cv tv Wp L
          let R := addressPositive cv tv raw L
          let updated := frontendInputs i L v
          let Rp := rankPartitionedAddress cv tv g raw L
          let N := completeRankEven i (addressRank g) Rp
          let final := selectRankInputs i (addressRank g) updated
          ActualRoot (NumberedWindowConcreteCheckers.root entries s) root ∧ ActualFallback other ∧
          ActualTermExchange s base ∧ ActualTermExchange s Xm ∧
          ActualPackedWindow s baseW ∧ ActualPackedWindow s Wp ∧
          ActualLeastCalibration s baseL ∧ ActualLeastCalibration s L ∧
          CallbacksAt entries s cv tv raw L ∧ ActualScalarCalibration s i ∧
          chosenA updated = chosenA v ∧ updated.applicationGuard = guard i (applicationCore L) ∧
          TupleAt entries s W i (jRaw i) R (dCore i R permutation) updated ∧
          InstalledReportAt i (jRaw i) cv tv (dCore i R permutation) raw L ∧
          chosenA final = chosenA v ∧
          final.applicationGuard = rankApplication i (addressRank g) (guard i (applicationCore L)) ∧
          TupleAt entries s W i (jRaw i) N (dCore i N permutation) final ∧
          (∀ c, FreshVariablesComputable (data i (jRaw i) N (dCore i N permutation))
            final.applicationGuard (chosenH final W) (chosenA final) c) := by
  obtain ⟨g,V,TV,baseM,rankFit,hV,hTV,hVa,hBaseM,hCombine,hM,hGrammar,hC,pick⟩ := NumberedWindowInternalMeasuredSelectedGrammarCheckedLeastChoiceProof.selected
  let Va := auxSyntax V TV
  let C := factoredCover Va (selectedMeasure (measureUpdate baseM chosenCombine)) selectedGrammarOption
  refine ⟨g,V,TV,baseM,rankFit,hV,hTV,hVa,hBaseM,hCombine,hM,hGrammar,hC,?_⟩
  intro entries s W valid symmetric covered outScalar
  obtain ⟨cv,tv,base,primitiveW,T,root,other,v,hroot,hother,hbase,hXm,hBaseW,hWp,
    baseFit,checkedFit,callbacks,scalar,keeps,guardEq,baseTuple,baseReport,_⟩ :=
    pick entries s W valid symmetric covered
  let Wp := window C s (intrinsicQuery (selectedIntrinsic (windowUpdate primitiveW T))) Va
  let Xm := measuredFactoredExchange s base Va baseM chosenCombine selectedGrammarOption
  let raw := typedRaw5 root other Wp Va
  let L := checkedLeast g (packedLeastProgram C Xm Wp s)
  let i := addressScalar cv tv Wp L
  let R := addressPositive cv tv raw L
  let updated := frontendInputs i L v
  obtain ⟨keeps',guardEq',installed,fresh⟩ := reselectRankApplication entries s W valid
    i (jRaw i) cv tv g R (dCore i R permutation) (applicationCore L) L raw updated
    baseTuple guardEq callbacks rankFit outScalar
  exact ⟨cv,tv,base,primitiveW,T,root,other,v,hroot,hother,hbase,hXm,hBaseW,hWp,
    baseFit,checkedFit,callbacks,scalar,keeps,guardEq,baseTuple,baseReport,keeps'.trans keeps,guardEq',installed,fresh⟩

#print axioms selected
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredSelectedGrammarCheckedLeastPartitionedRankChoiceProof
