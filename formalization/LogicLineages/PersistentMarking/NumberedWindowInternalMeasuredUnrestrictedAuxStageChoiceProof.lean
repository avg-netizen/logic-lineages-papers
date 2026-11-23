module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedNumericChoiceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverGrammarStageTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverGrammarStageNumericThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredCoverNumericProof
import LogicLineages.PersistentMarking.NumberedWindowAddressProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowNumericProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedAuxStageChoiceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated GrammarOptionCalibrated factoredCover)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax ActualPackedWindow)
open NumberedWindowInternalSparseRawTickTargets (ActualRoot ActualFallback)
open NumberedWindowInternalAuxWindowStepTargets (intrinsicQuery windowUpdate)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof
  (measuredFactoredExchange exact_LiteralMeasuredFactoredCalibration)
open NumberedWindowInternalAuxExchangeMemoStepChecks (exact_PhysicalAuxMemoExchange)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (WindowSeedsCovered window syntaxWindow)
open NumberedWindowInternalMeasuredUnrestrictedWindowNumericProof
  (exact_SyntaxWindowCalibration exact_LiteralCoveredWindowCalibration)
open NumberedWindowInternalMeasuredUnrestrictedNumericChoiceProof (exact_OriginalMeasuredUnrestrictedNumericChoice)
open NumberedWindowAddressProgramChecks (exact_TypeCodeProgram)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntax)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (TypeSyntaxCalibrated)
open NumberedWindowInternalCoverAuxSyntaxNumericProof (exact_CoverAuxSyntaxCalibration)
open NumberedWindowInternalCoverGrammarStageTargets (stageGenerator LayerPartsCalibrated)
open NumberedWindowInternalCoverGrammarStageNumericThinProof (exact_SelectedGrammarStage)

/-- Fresh original numeric fitting using the actual open stage generator,
not a graph replacement for the opaque old grammar. The old selected
measure and the original raw and window source callbacks are retained. -/
theorem exact_OriginalMeasuredUnrestrictedAuxStageChoice :
    ∃ (V TV baseM : Program 1) (P : Program 2)
      (nonAux : Program 5) (nextArgs : Program 2),
      let Va := auxSyntax V TV
      let G := stageGenerator nonAux nextArgs
      let M := selectedMeasure (measureUpdate baseM P)
      let C := factoredCover Va M G
      ActualRawSyntax V ∧ TypeSyntaxCalibrated TV ∧ ActualRawSyntax Va ∧
      TermMeasureCalibrated M ∧ LayerPartsCalibrated nonAux nextArgs ∧
      GrammarOptionCalibrated G ∧ ActualSelectedCoverOutput C ∧
      ∀ (entries : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
        HeadPairsSymmetric s.equivalentHeads → WindowSeedsCovered s →
        ∃ (base primitiveW : Program 2) (TW : Program 1) (root other : Program 3),
          let baseW := intrinsicQuery (selectedIntrinsic (windowUpdate primitiveW TW))
          let Wp := window C s baseW Va
          ActualRoot (NumberedWindowConcreteCheckers.root entries s) root ∧ ActualFallback other ∧
          ActualTermExchange s base ∧ ActualTermExchange s (measuredFactoredExchange s base Va baseM P G) ∧
          ActualPackedWindow s baseW ∧ ActualPackedWindow s Wp := by
  obtain ⟨V,baseM,P,_,oldFit,measure,_,choose⟩ := exact_OriginalMeasuredUnrestrictedNumericChoice
  obtain ⟨TV,codeFit⟩ := exact_TypeCodeProgram
  have typeFit : TypeSyntaxCalibrated TV := codeFit
  obtain ⟨nonAux,nextArgs,stageParts,grammarFit⟩ := exact_SelectedGrammarStage
  let Va := auxSyntax V TV
  let G := stageGenerator nonAux nextArgs
  let M := selectedMeasure (measureUpdate baseM P)
  let C := factoredCover Va M G
  have syntaxFit : ActualRawSyntax Va := exact_CoverAuxSyntaxCalibration V TV oldFit typeFit
  have coverFit : ActualSelectedCoverOutput C :=
    NumberedWindowInternalFactoredCoverNumericProof.calibration Va M G syntaxFit measure grammarFit
  refine ⟨V,TV,baseM,P,nonAux,nextArgs,oldFit,typeFit,syntaxFit,measure,stageParts,grammarFit,coverFit,?_⟩
  intro entries s W hW symmetric covered
  obtain ⟨base,primitiveW,TW,root,other,hroot,hother,hbase,_,w,_⟩ := choose entries s W hW symmetric covered
  let baseW := intrinsicQuery (selectedIntrinsic (windowUpdate primitiveW TW))
  have directed := exact_PhysicalAuxMemoExchange s base Va hbase syntaxFit
  have exchanged := exact_LiteralMeasuredFactoredCalibration s base Va baseM P G
    symmetric coverFit measure directed
  have syntaxWindowFit := exact_SyntaxWindowCalibration s baseW Va w syntaxFit
  have combined := exact_LiteralCoveredWindowCalibration C s (syntaxWindow baseW Va)
    coverFit covered syntaxWindowFit
  exact ⟨base,primitiveW,TW,root,other,hroot,hother,hbase,exchanged,w,combined⟩

#print axioms exact_OriginalMeasuredUnrestrictedAuxStageChoice
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedAuxStageChoiceProof
