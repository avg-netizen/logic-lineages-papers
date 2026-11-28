module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaObservedBaseDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedLambdaBaseFitProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNormalizedAuxSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowMemoChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureStepChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalSourceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredCoverChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumNumericStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaObservedBaseNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch conjunction constantZero)
open InternalAcceptanceCalibrationProof (evalBranch evalNormalize actualConjunctionEvaluation)
open NumberedWindowScalarAlgorithm (Settings admitted)
open NumberedWindowFieldAlgorithm (pack unpackNode)
open NumberedWindowLexicalAlgorithm (typed)
open NumberedWindowAtomicRawStepFieldProof (unpackPacked)
open NumberedWindowInternalAuxWindowMemoTargets (IntrinsicWindowCalibrated intrinsicWindow intrinsicType)
open NumberedWindowInternalAuxWindowMemoChecks (exact_PackedIntrinsicProjection)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated)
open NumberedWindowInternalAuxExchangeMemoStepDataProof (conjunctionOne)
open NumberedWindowInternalAuxExchangeMemoStepTargets (TermSyntaxCalibrated)
open NumberedWindowInternalAuxMeasureStepChecks (exact_PhysicalAuxMeasure)
open NumberedWindowInternalCoverAuxApplicationsTargets (binary)
open NumberedWindowInternalCoverHeaderFieldsNumericProof (exact_CoverHeaderUnpackNode)
open NumberedWindowInternalCoverLambdaLexicalSourceProof (exact_CoverLambdaPackedLexicalProvenance)
open NumberedWindowInternalCoverLambdaLexicalWindowNumericProof (exact_LambdaLexicalFieldReads)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (lambdaLexicalPush precedingBase lambdaLexicalBase)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (TypeSyntaxCalibrated)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredTargets (chosenMeasure)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverSelectedGrammarOptionTargets (selectedGrammarOption)
open NumberedWindowInternalCoverSelectedGrammarOptionNumericProof (exact_SelectedGrammarOption)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open NumberedWindowInternalChosenAuxMeasureCombine (callOne chosenCombine)
open NumberedWindowInternalChosenAuxMeasureCombineNumericProof (exact_ChosenAuxMeasureCombine)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated)
open NumberedWindowInternalFactoredCoverChecks (exact_FactoredCoverCalibration)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeTwo vectorThree)
open NumberedWindowInternalLiteralCoveredMemo (contextPresent ownSeed WindowSeedsCovered)
open NumberedWindowInternalLiteralCoveredMemoNumericProof (exact_CoveredMemoCoverageAtPacked)
open NumberedWindowInternalLiteralJoinedLambdaBaseFitProof (exact_JoinedLambdaDecoratedBaseFit)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax exact_LiteralUnitAuxSyntax)
open NumberedWindowInternalSettingsGrammarGuardNumericTargets (GrammarTypeInclusion)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseOrderedMinimumNumericStepProof (unaryValue)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePairEvaluationProof (consValue)
open NumberedWindowInternalSparsePathEnvelope (run field nodeGood)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (packOfUnpack)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax packedWindow)
open NumberedWindowInternalLiteralLambdaObservedBase

theorem exact_ObservedLambdaBaseCalibration (C : Program 3) (s : Settings) (Va : Program 1)
    (base : Program 2) (cover : ActualSelectedCoverOutput C) (seeds : WindowSeedsCovered s)
    (vaFit : ActualRawSyntax Va) (baseFit : IntrinsicWindowCalibrated s base) :
    IntrinsicWindowCalibrated s (observedLambdaBase C s Va base) := by
  intro ctx raw
  let xs := ctx ::ᵥ raw ::ᵥ nil
  change evaluate (observedLambdaBase C s Va base) xs = intrinsicWindow s ctx raw
  rw [observedLambdaBase,evalBranch]
  change (if run (header 2 2) raw = 0 then evaluate base xs else
    evaluate (branch (normalize (lambdaChildObservations C s Va)) (constantZero 2) base) xs) = _
  by_cases noLambda : run (header 2 2) raw = 0
  · rw [if_pos noLambda]
    exact baseFit ctx raw
  rw [if_neg noLambda,evalBranch,baseFit ctx raw]
  by_cases zero : intrinsicWindow s ctx raw = 0
  · rw [zero]
    split <;> rfl
  have bits : run (header 2 2) raw = 0 ∨ run (header 2 2) raw = 1 := by
    unfold run header nodeGood
    rw [actualConjunctionEvaluation]
    split <;> simp
  obtain ⟨fs,parse,len⟩ := (exact_CoverHeaderUnpackNode 2 2 raw).mp (bits.resolve_left noLambda)
  rcases fs with _ | ⟨dom,_ | ⟨q,_ | ⟨extra,rest⟩⟩⟩ <;> simp at len
  obtain ⟨g,unpackCtx,_,child,_⟩ :=
    exact_CoverLambdaPackedLexicalProvenance s ctx raw dom q parse zero
  let pushed := pack (dom :: g)
  have childWindow : packedWindow s pushed (intrinsicType q) q = true := by
    rw [exact_PackedIntrinsicProjection s pushed (intrinsicType q) q,child] <;> simp
  have admittedChild : admitted s (dom :: g) (intrinsicType q) q = true := by
    simpa [pushed,packedWindow,unpackPacked] using childWindow
  have syntaxBit : (NumberedWindowSyntaxAlgorithm.syntaxBits q).1 = true := by
    simp only [admitted,typed,Bool.and_eq_true] at admittedChild
    exact admittedChild.1.1.1
  obtain ⟨domRead,childRead⟩ := exact_LambdaLexicalFieldReads parse
  have push : evaluate lambdaLexicalPush xs = pushed := by
    rw [lambdaLexicalPush,binary,compositeTwo]
    change evaluate fieldCons (run (field 0) raw ::ᵥ ctx ::ᵥ nil) = _
    rw [domRead,packOfUnpack ctx unpackCtx,consValue] <;> rfl
  have childAt : evaluate (onRaw (field 1)) xs = q := childRead
  have covered : evaluate (lambdaChildCoverage C s) xs = 1 := by
    rw [lambdaChildCoverage,evaluate,vectorThree]
    change evaluate (conjunction contextPresent (ownSeed C s))
      (evaluate lambdaLexicalPush xs ::ᵥ 0 ::ᵥ evaluate (onRaw (field 1)) xs ::ᵥ nil) = 1
    rw [push,childAt]
    exact exact_CoveredMemoCoverageAtPacked C s cover seeds pushed (intrinsicType q) 0 q childWindow
  have wellFormed : evaluate (lambdaChildSyntax Va) xs = 1 := by
    rw [lambdaChildSyntax,callOne,unaryValue,childAt,vaFit q,syntaxBit] <;> rfl
  have accepted : evaluate (lambdaChildObservations C s Va) xs = 1 :=
    (conjunctionOne (lambdaChildCoverage C s) (lambdaChildSyntax Va) xs).mpr ⟨covered,wellFormed⟩
  rw [evalNormalize,accepted] <;> simp

/-- Calibrate the callback with the selected measured cover and unit syntax
program that occur in the literal joined memo packet. -/
theorem exact_MeasuredObservedLambdaBaseFit (s : Settings) (V TV baseM : Program 1)
    (grammar : GrammarTypeInclusion s) (seeds : WindowSeedsCovered s)
    (vFit : TermSyntaxCalibrated V) (tvFit : TypeSyntaxCalibrated TV)
    (mFit : TermMeasureCalibrated baseM) :
    ∃ (seed : Program 2) (T : Program 1),
      let Va := unitAuxSyntax V TV
      let C := selectedCover Va (chosenMeasure baseM)
      IntrinsicWindowCalibrated s (observedLambdaBase C s Va (precedingBase s (lambdaLexicalBase s seed T))) ∧
      TypeGuardCalibrated s T := by
  obtain ⟨seed,T,baseFit,tFit⟩ := exact_JoinedLambdaDecoratedBaseFit s grammar
  have vaFit := exact_LiteralUnitAuxSyntax V TV vFit tvFit
  have measureFit := exact_PhysicalAuxMeasure baseM chosenCombine mFit exact_ChosenAuxMeasureCombine
  have coverFit := exact_FactoredCoverCalibration (unitAuxSyntax V TV) (chosenMeasure baseM)
    selectedGrammarOption vaFit measureFit exact_SelectedGrammarOption
  exact ⟨seed,T,exact_ObservedLambdaBaseCalibration _ s _ _ coverFit seeds vaFit baseFit,tFit⟩

#print axioms exact_ObservedLambdaBaseCalibration
#print axioms exact_MeasuredObservedLambdaBaseFit
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaObservedBaseNumericProof
