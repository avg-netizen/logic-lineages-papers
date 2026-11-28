module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowStepPrograms
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedTypeWindowNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedResultNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalBoundWindowNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafIntrinsicNumericProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedLambdaBaseFitProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSettingsGrammarGuardNumericTargets (GrammarTypeInclusion)
open NumberedWindowInternalAuxWindowMemoTargets (IntrinsicWindowCalibrated)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated)
open NumberedWindowInternalAuxWindowStepPrograms (exact_WindowPrimitiveLeaves)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (precedingBase lambdaLexicalBase)
open NumberedWindowInternalCoverLambdaLexicalWindowNumericProof (exact_CoverLambdaLexicalBase)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeBase)
open NumberedWindowInternalCoverNumberedTypeWindowNumericProof (exact_CoverNumberedTypeBase)
open NumberedWindowInternalCoverHeadWindowTargets (grammarHeadBase)
open NumberedWindowInternalCoverHeadWindowNumericProof (exact_CoverGrammarHeadBase)
open NumberedWindowInternalCoverNamedResultTargets (namedResultAt namedResultBase)
open NumberedWindowInternalCoverNamedResultNumericProof (exact_CoverNamedResultAt)
open NumberedWindowInternalCoverLexicalBoundWindowTargets (lexicalBoundBase)
open NumberedWindowInternalCoverLexicalBoundWindowNumericProof (exact_CoverLexicalBoundBase)
open NumberedWindowInternalCoverNamedLeafIntrinsicTargets (namedGrammarAt namedGrammarBase)
open NumberedWindowInternalCoverNamedLeafIntrinsicNumericProof (exact_CoverNamedLeafGrammarAt)
open NumberedWindowInternalCoverTypeLeafIntrinsicNumericProof (exact_CoverTypeLeafIntrinsicBase)

/-- The base callback required by the joined lambda child-window proof
is calibrated with the packet's own settings and a calibrated type guard. -/
theorem exact_JoinedLambdaDecoratedBaseFit (s : Settings) (grammar : GrammarTypeInclusion s) :
    ∃ (seed : Program 2) (T : Program 1),
      IntrinsicWindowCalibrated s (precedingBase s (lambdaLexicalBase s seed T)) ∧
      TypeGuardCalibrated s T := by
  obtain ⟨seed,T,seedFit,tFit⟩ := exact_WindowPrimitiveLeaves s
  let lambdaBase := lambdaLexicalBase s seed T
  let headBase := grammarHeadBase s (numberedTypeBase s lambdaBase)
  let boundBase := lexicalBoundBase (namedResultBase headBase)
  have lambdaFit := exact_CoverLambdaLexicalBase s seed T grammar seedFit tFit
  have headFit := exact_CoverGrammarHeadBase s (numberedTypeBase s lambdaBase)
    (exact_CoverNumberedTypeBase s lambdaBase grammar lambdaFit)
  have namedFit := exact_CoverNamedResultAt false s (namedResultAt true headBase)
    (exact_CoverNamedResultAt true s headBase headFit)
  have boundFit := exact_CoverLexicalBoundBase s (namedResultBase headBase) namedFit
  have grammarFit := exact_CoverNamedLeafGrammarAt false s (namedGrammarAt true s boundBase) grammar
    (exact_CoverNamedLeafGrammarAt true s boundBase grammar boundFit)
  have fit := exact_CoverTypeLeafIntrinsicBase s (namedGrammarBase s boundBase) grammar grammarFit
  exact ⟨seed,T,fit,tFit⟩

#print axioms exact_JoinedLambdaDecoratedBaseFit
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedLambdaBaseFitProof
