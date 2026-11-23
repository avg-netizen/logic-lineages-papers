module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedNumericChoiceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedAuxSyntaxRetargetProof
import LogicLineages.PersistentMarking.NumberedWindowAddressProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowNumericProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedAuxSyntaxChoiceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
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
open NumberedWindowInternalAuxExchangeMemoStepChecks (exact_PhysicalAuxMemoExchange)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (WindowSeedsCovered window syntaxWindow)
open NumberedWindowInternalMeasuredUnrestrictedWindowNumericProof
  (exact_SyntaxWindowCalibration exact_LiteralCoveredWindowCalibration)
open NumberedWindowInternalMeasuredUnrestrictedNumericChoiceProof (exact_OriginalMeasuredUnrestrictedNumericChoice)
open NumberedWindowAddressProgramChecks (exact_TypeCodeProgram)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntax)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (TypeSyntaxCalibrated)
open NumberedWindowInternalMeasuredUnrestrictedAuxSyntaxRetargetProof

/-- A fresh unrestricted numeric choice, not a conversion of old open
formulas. The original measure/grammar and all base callbacks remain.
TV detects original raw type syntax; TW is the independently chosen
contextual window type guard. -/
theorem exact_OriginalMeasuredUnrestrictedAuxSyntaxChoice :
    ∃ (V TV baseM : Program 1) (P : Program 2) (G : Program 3),
      let Va := auxSyntax V TV
      let M := selectedMeasure (measureUpdate baseM P)
      let C := factoredCover Va M G
      ActualRawSyntax V ∧ TypeSyntaxCalibrated TV ∧ ActualRawSyntax Va ∧
      TermMeasureCalibrated M ∧ ActualSelectedCoverOutput C ∧
      ∀ (entries : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
        HeadPairsSymmetric s.equivalentHeads → WindowSeedsCovered s →
        ∃ (base primitiveW : Program 2) (TW : Program 1) (root other : Program 3),
          let baseW := intrinsicQuery (selectedIntrinsic (windowUpdate primitiveW TW))
          let Wp := window C s baseW Va
          ActualRoot (NumberedWindowConcreteCheckers.root entries s) root ∧ ActualFallback other ∧
          ActualTermExchange s base ∧ ActualTermExchange s (measuredFactoredExchange s base Va baseM P G) ∧
          ActualPackedWindow s baseW ∧ ActualPackedWindow s Wp := by
  obtain ⟨V,baseM,P,G,oldFit,measure,oldCover,choose⟩ := exact_OriginalMeasuredUnrestrictedNumericChoice
  obtain ⟨TV,codeFit⟩ := exact_TypeCodeProgram
  have typeFit : TypeSyntaxCalibrated TV := codeFit
  let Va := auxSyntax V TV
  let M := selectedMeasure (measureUpdate baseM P)
  let C := factoredCover Va M G
  have syntaxFit : ActualRawSyntax Va := exact_OriginalUnrestrictedAuxSyntaxCalibration V TV oldFit typeFit
  have coverFit : ActualSelectedCoverOutput C := exact_OriginalUnrestrictedAuxCoverFit V TV M G oldFit typeFit oldCover
  refine ⟨V,TV,baseM,P,G,oldFit,typeFit,syntaxFit,measure,coverFit,?_⟩
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

#print axioms exact_OriginalMeasuredUnrestrictedAuxSyntaxChoice
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedAuxSyntaxChoiceProof
