module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredPairedGuardedThinNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowStepTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationTargets

public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedPrimitiveChoiceProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedNumericChoiceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure CombineCalibrated)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated factoredCover)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax ActualPackedWindow)
open NumberedWindowInternalSparseRawTickTargets (ActualRoot ActualFallback)
open NumberedWindowInternalAuxWindowStepTargets (intrinsicQuery windowUpdate)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof
  (measuredFactoredExchange exact_LiteralMeasuredFactoredCalibration)

open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (WindowSeedsCovered window syntaxWindow)
open NumberedWindowInternalMeasuredUnrestrictedWindowNumericProof
  (exact_SyntaxWindowCalibration exact_LiteralCoveredWindowCalibration)
open NumberedWindowInternalMeasuredUnrestrictedPrimitiveChoiceProof (exact_OriginalMeasuredUnrestrictedPrimitiveChoice)

/-- One original unrestricted physical C/X/W selection, retaining the
literal window inputs and actual original root/fallback. -/
theorem exact_OriginalMeasuredUnrestrictedNumericChoice :
    ∃ (V baseM : Program 1) (P : Program 2) (G : Program 3),
      let M := selectedMeasure (measureUpdate baseM P)
      let C := factoredCover V M G
      ActualRawSyntax V ∧ TermMeasureCalibrated M ∧ ActualSelectedCoverOutput C ∧
      ∀ (entries : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
        HeadPairsSymmetric s.equivalentHeads → WindowSeedsCovered s →
        ∃ (base primitiveW : Program 2) (T : Program 1) (root other : Program 3),
          let baseW := intrinsicQuery (selectedIntrinsic (windowUpdate primitiveW T))
          let Wp := window C s baseW V
          ActualRoot (NumberedWindowConcreteCheckers.root entries s) root ∧ ActualFallback other ∧
          ActualTermExchange s base ∧ ActualTermExchange s (measuredFactoredExchange s base V baseM P G) ∧
          ActualPackedWindow s baseW ∧ ActualPackedWindow s Wp := by
  obtain ⟨V,baseM,P,G,valid,measure,cover,choose⟩ := exact_OriginalMeasuredUnrestrictedPrimitiveChoice
  refine ⟨V,baseM,P,G,valid,measure,cover,?_⟩
  intro entries s W hW symmetric covered
  obtain ⟨base,primitiveW,T,root,other,hroot,hother,hbase,exchanged,w⟩ := choose entries s W hW symmetric
  let baseW := intrinsicQuery (selectedIntrinsic (windowUpdate primitiveW T))
  let C := factoredCover V (selectedMeasure (measureUpdate baseM P)) G
  have syntaxFit := exact_SyntaxWindowCalibration s baseW V w valid
  have combined := exact_LiteralCoveredWindowCalibration C s (syntaxWindow baseW V) cover covered syntaxFit
  exact ⟨base,primitiveW,T,root,other,hroot,hother,hbase,exchanged,w,combined⟩

#print axioms exact_OriginalMeasuredUnrestrictedNumericChoice
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedNumericChoiceProof
