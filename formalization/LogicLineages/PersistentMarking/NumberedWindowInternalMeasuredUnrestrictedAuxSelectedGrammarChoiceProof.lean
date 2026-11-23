module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedNumericChoiceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedChosenCombineProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionNumericProof
import LogicLineages.PersistentMarking.NumberedWindowAddressProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowNumericProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedAuxSelectedGrammarChoiceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure CombineCalibrated)
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
open NumberedWindowInternalCoverSelectedGrammarOptionTargets (selectedGrammarOption)
open NumberedWindowInternalCoverSelectedGrammarOptionNumericProof
  (exact_SelectedGrammarOption exact_SelectedGrammarFactoredCover)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalMeasuredUnrestrictedChosenCombineProof
  (exact_OriginalMeasuredUnrestrictedChosenCombine)

/-- Select the actual physical auxiliary syntax, open-arithmetic measure,
and cross-bound selected grammar together. Numeric fitting is fresh;
no graph from the old choice is rewritten under extensional equality. -/
theorem exact_OriginalMeasuredUnrestrictedAuxSelectedGrammarChoice :
    ∃ (V TV baseM : Program 1),
      let Va := auxSyntax V TV
      let M := selectedMeasure (measureUpdate baseM chosenCombine)
      let C := factoredCover Va M selectedGrammarOption
      ActualRawSyntax V ∧ TypeSyntaxCalibrated TV ∧ ActualRawSyntax Va ∧
      TermMeasureCalibrated baseM ∧ CombineCalibrated chosenCombine ∧
      TermMeasureCalibrated M ∧ GrammarOptionCalibrated selectedGrammarOption ∧
      ActualSelectedCoverOutput C ∧
      ∀ (entries : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
        HeadPairsSymmetric s.equivalentHeads → WindowSeedsCovered s →
        ∃ (base primitiveW : Program 2) (TW : Program 1) (root other : Program 3),
          let baseW := intrinsicQuery (selectedIntrinsic (windowUpdate primitiveW TW))
          let Wp := window C s baseW Va
          ActualRoot (NumberedWindowConcreteCheckers.root entries s) root ∧ ActualFallback other ∧
          ActualTermExchange s base ∧ ActualTermExchange s (measuredFactoredExchange s base Va baseM chosenCombine selectedGrammarOption) ∧
          ActualPackedWindow s baseW ∧ ActualPackedWindow s Wp := by
  obtain ⟨V,_,_,_,oldFit,_,_,choose⟩ := exact_OriginalMeasuredUnrestrictedNumericChoice
  obtain ⟨TV,codeFit⟩ := exact_TypeCodeProgram
  have typeFit : TypeSyntaxCalibrated TV := codeFit
  obtain ⟨baseM,baseFit,combineFit,measure⟩ := exact_OriginalMeasuredUnrestrictedChosenCombine
  let Va := auxSyntax V TV
  let M := selectedMeasure (measureUpdate baseM chosenCombine)
  let C := factoredCover Va M selectedGrammarOption
  have syntaxFit : ActualRawSyntax Va := exact_CoverAuxSyntaxCalibration V TV oldFit typeFit
  have coverFit : ActualSelectedCoverOutput C := exact_SelectedGrammarFactoredCover Va M syntaxFit measure
  refine ⟨V,TV,baseM,oldFit,typeFit,syntaxFit,baseFit,combineFit,measure,exact_SelectedGrammarOption,coverFit,?_⟩
  intro entries s W hW symmetric covered
  obtain ⟨base,primitiveW,TW,root,other,hroot,hother,hbase,_,w,_⟩ := choose entries s W hW symmetric covered
  let baseW := intrinsicQuery (selectedIntrinsic (windowUpdate primitiveW TW))
  have directed := exact_PhysicalAuxMemoExchange s base Va hbase syntaxFit
  have exchanged := exact_LiteralMeasuredFactoredCalibration s base Va baseM chosenCombine selectedGrammarOption
    symmetric coverFit measure directed
  have syntaxWindowFit := exact_SyntaxWindowCalibration s baseW Va w syntaxFit
  have combined := exact_LiteralCoveredWindowCalibration C s (syntaxWindow baseW Va)
    coverFit covered syntaxWindowFit
  exact ⟨base,primitiveW,TW,root,other,hroot,hother,hbase,exchanged,w,combined⟩

#print axioms exact_OriginalMeasuredUnrestrictedAuxSelectedGrammarChoice
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedAuxSelectedGrammarChoiceProof
