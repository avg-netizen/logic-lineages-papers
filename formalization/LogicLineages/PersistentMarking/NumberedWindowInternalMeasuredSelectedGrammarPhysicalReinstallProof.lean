module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedAuxSelectedGrammarChoiceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPhysicalScalarReinstallProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTuplePresentationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleReportProof
import LogicLineages.PersistentMarking.NumberedWindowGuardedGraphChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredSelectedGrammarPhysicalReinstallProof

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFormulaCalibrationTargets (Evaluates)
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ChildClosed ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenH chosenA)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax ActualPackedWindow)
open NumberedWindowInternalSparseRawTickTargets (ActualRoot ActualFallback)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration)
open NumberedWindowInternalSparseAddressPositiveCalibrationTargets
  (ActualAddressPositiveCalibration ActualContextGuard ActualTypeGuard)
open NumberedWindowInternalSparseTuple (CallbacksAt InstalledTupleAt InstalledReportAt)
open NumberedWindowInternalSparseTuplePresentationProof (rebuild)
open NumberedWindowInternalSparseTupleReportProof (installed)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalAtomicRefinement (refined)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalProbeTargets (TypedProbeTotal)
open NumberedWindowGuardedGraphTargets (guard InputGuards)
open NumberedWindowGuardedGraphChecks (exact_GuardRules)
open NumberedWindowInternalFreshProbeParsedTypedObjectChecks (exact_SameParsedTypedProbeTotal)
open NumberedWindowInternalFreshProbeAlignmentChecks (exact_GivenFreshAlignmentAndCarriers)
open NumberedWindowInternalLiteralPhysicalScalarReinstallProof (exact_ReinstallLiteralPhysicalScalar)
open NumberedWindowInternalSparseLeastInstallationChecks (exact_PhysicalLeastInstalledTuple)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalSparseApplicationReinstall (frontendInputs)
open NumberedWindowInternalSparseApplicationFrontend (applicationCore)
open NumberedWindowInternalSparseApplicationFrontendTargets (ActualScalarCalibration)
open NumberedWindowInternalSparsePackedLeastNumericChecks (exact_PackedLeastComposition)
open NumberedWindowInternalSparseTypedRawChecks (exact_TypedRaw5Calibration)
open NumberedWindowInternalSparsePathAdvanceNumericChecks (exact_AdvanceComposition)
open NumberedWindowInternalSparsePositiveFoldNumericChecks (exact_FoldComposition)
open NumberedWindowInternalSparseAddressPositiveNumericChecks (exact_AddressPositiveComposition)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure CombineCalibrated)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated GrammarOptionCalibrated factoredCover)
open NumberedWindowInternalAuxWindowStepTargets (intrinsicQuery windowUpdate)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (measuredFactoredExchange)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (WindowSeedsCovered window)
open NumberedWindowInternalMeasuredUnrestrictedAuxSelectedGrammarChoiceProof (exact_OriginalMeasuredUnrestrictedAuxSelectedGrammarChoice)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntax)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (TypeSyntaxCalibrated)
open NumberedWindowInternalCoverSelectedGrammarOptionTargets (selectedGrammarOption)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)

private theorem rebuildChangedRaw (entries : Entries) (s : Settings) (W : List ProbeTy)
    (closed : ChildClosed W) (i j cv tv : Program 1) (old d p₀ least : Program 3)
    (raw : Program 5) (v : Inputs) (prior : TupleAt entries s W i j old d v)
    (guardEq : v.applicationGuard = guard i p₀)
    (cal : ActualAddressPositiveCalibration entries s cv tv raw least)
    (callbacks : CallbacksAt entries s cv tv raw least) :
    InstalledTupleAt entries s W i j cv tv d p₀ raw least v := by
  let R := addressPositive cv tv raw least
  let S := data i j R d
  obtain ⟨oldValues,_,_,inputCal,unique,_,aCal,hCal,_,shape,_⟩ := prior
  have values : Evaluates (checks entries s) i j R d :=
    ⟨oldValues.1,oldValues.2.1,cal,oldValues.2.2.2⟩
  obtain ⟨values,meaning,rules⟩ := rebuild entries s i j R d values
  have guards : InputGuards i j R d v.applicationGuard := by
    rw [guardEq]
    exact (exact_GuardRules i j R d p₀).1
  have total (c : Nat) : TypedProbeTotal S v.applicationGuard (chosenH v W) (chosenA v) c :=
    exact_SameParsedTypedProbeTotal v W closed S c
  have tuple : TupleAt entries s W i j R d v :=
    ⟨values,meaning,rules,inputCal,unique,guards,aCal,hCal,total,shape,
      fun c => exact_GivenFreshAlignmentAndCarriers i j R d v.applicationGuard
        (chosenH v W) (chosenA v) c guards (total c)⟩
  exact ⟨tuple,guardEq,callbacks,installed i j cv tv d raw least⟩

/-- Install one measured physical window and measured exchange into the
very same original least, raw validator, scalar, application and positive
programs. The new scalar and both source bodies are built from numerical
calibrations; the original open report is freshly produced for the new R. -/
theorem selected :
    ∃ (V TV baseM : Program 1),
      let Va := auxSyntax V TV
      let M := selectedMeasure (measureUpdate baseM chosenCombine)
      let C := factoredCover Va M selectedGrammarOption
      ActualRawSyntax V ∧ TypeSyntaxCalibrated TV ∧ ActualRawSyntax Va ∧
      TermMeasureCalibrated baseM ∧ CombineCalibrated chosenCombine ∧
      TermMeasureCalibrated M ∧ GrammarOptionCalibrated selectedGrammarOption ∧ ActualSelectedCoverOutput C ∧
      ∀ (entries : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
        HeadPairsSymmetric s.equivalentHeads → WindowSeedsCovered s →
        ∃ (cv tv : Program 1) (base primitiveW : Program 2) (T : Program 1)
          (root other : Program 3) (v : Inputs),
          let baseW := intrinsicQuery (selectedIntrinsic (windowUpdate primitiveW T))
          let Wp := window C s baseW Va
          let Xm := measuredFactoredExchange s base Va baseM chosenCombine selectedGrammarOption
          let raw := typedRaw5 root other Wp Va
          let L := packedLeastProgram C Xm Wp s
          let i := addressScalar cv tv Wp L
          let R := addressPositive cv tv raw L
          let RR := refined i R
          let updated := frontendInputs i L v
          ActualRoot (NumberedWindowConcreteCheckers.root entries s) root ∧ ActualFallback other ∧
          ActualTermExchange s base ∧ ActualTermExchange s Xm ∧
          ActualPackedWindow s baseW ∧ ActualPackedWindow s Wp ∧
          CallbacksAt entries s cv tv raw L ∧ ActualScalarCalibration s i ∧
          chosenA updated = chosenA v ∧ updated.applicationGuard = guard i (applicationCore L) ∧
          TupleAt entries s W i (jRaw i) R (dCore i R permutation) updated ∧
          InstalledReportAt i (jRaw i) cv tv (dCore i R permutation) raw L ∧
          TupleAt entries s W i (jRaw i) RR (dCore i RR permutation) updated := by
  obtain ⟨V,TV,baseM,hV,hTV,hVa,hBaseM,hCombine,hM,hGrammar,hC,pick⟩ :=
    exact_OriginalMeasuredUnrestrictedAuxSelectedGrammarChoice
  let Va := auxSyntax V TV
  let C := factoredCover Va (selectedMeasure (measureUpdate baseM chosenCombine)) selectedGrammarOption
  refine ⟨V,TV,baseM,hV,hTV,hVa,hBaseM,hCombine,hM,hGrammar,hC,?_⟩
  intro entries s W valid symmetric covered
  obtain ⟨base,primitiveW,T,root,other,hroot,hother,hbase,hXm,hBaseW,hWp⟩ :=
    pick entries s W valid symmetric covered
  obtain ⟨_,_,oldPick⟩ := exact_PhysicalLeastInstalledTuple
  obtain ⟨oldI,j,cv,tv,oldV,_,d,core,oldL,oldRoot,oldOther,oldWp,v,
    _,_,_,_,_,_,oldTuple,_,_⟩ := oldPick entries s W valid
  let Wp := window C s (intrinsicQuery (selectedIntrinsic (windowUpdate primitiveW T))) Va
  let Xm := measuredFactoredExchange s base Va baseM chosenCombine selectedGrammarOption
  let raw := typedRaw5 root other Wp Va
  let L := packedLeastProgram C Xm Wp s
  obtain ⟨ctxFit,tyFit,_,_,_,_,_⟩ := oldTuple.2.2.1
  have leastFit := exact_PackedLeastComposition s C Xm Wp hC hXm hWp
  have rawFit := exact_TypedRaw5Calibration entries s root other Wp Va hroot hother hVa hWp
  have advance := exact_AdvanceComposition entries s raw L rawFit leastFit
  obtain ⟨fuel,positive⟩ := exact_FoldComposition entries s raw L advance
  have callbacks : CallbacksAt entries s cv tv raw L :=
    ⟨ctxFit,tyFit,rawFit,leastFit,advance,fuel,positive⟩
  have cal := exact_AddressPositiveComposition entries s cv tv raw L ctxFit tyFit positive
  let oldR := addressPositive cv tv (typedRaw5 oldRoot oldOther oldWp oldV) oldL
  have freshly := rebuildChangedRaw entries s W valid.2.1 oldI j cv tv oldR d core L raw v
    oldTuple.1 oldTuple.2.1 cal callbacks
  have installed := exact_ReinstallLiteralPhysicalScalar entries s W valid oldI j cv tv d
    core Wp raw L v hWp freshly
  exact ⟨cv,tv,base,primitiveW,T,root,other,v,hroot,hother,hbase,hXm,hBaseW,hWp,callbacks,installed⟩

#print axioms selected
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredSelectedGrammarPhysicalReinstallProof
