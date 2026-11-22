module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxInputsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxContextProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrapperProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedAuxSyntaxIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxIntroduceProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxChildren)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (precedingBase lambdaLexicalBase)
open NumberedWindowInternalCoverRefinedSharedSyntaxTargets (refinedAuxChildren)
open NumberedWindowInternalCoverStrictAuxIntroduceProof (exact_OpenCoverStrictAuxIntroduce)
open NumberedWindowInternalCoverRefinedAuxSyntaxIntroProof (exact_OpenCoverRefinedAuxSyntaxIntro)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedCallback)
open NumberedWindowInternalCoverCombinedRestrictedWrapperProof (exact_OpenCoverCombinedRestrictedWrapper)
open NumberedWindowInternalCoverCombinedRestrictedWrappedAuxInputsProof (exact_OpenCoverThinMatchingWindowInputs)
open NumberedWindowInternalCoverCombinedRestrictedWrappedAuxContextProof (exact_OpenCoverThinMatchingContextTransport)
open NumberedWindowInternalCoverCombinedRestrictedWrappedAuxTargets

theorem exact_OpenCoverCombinedWrappedAuxFormation : ExactOpenCoverCombinedWrappedAuxFormation := by
  intro V TV M M0 B T s body α Γ ctx dom cod fn arg P W syntaxGuards typedGuards function argument
  let D : Program 2 := combinedCallback s B
  let base : Program 2 := precedingBase s (lambdaLexicalBase s D T)
  let S : Program 1 := refitGuard s T
  let key := auxiliaryTerm dom cod fn arg
  let inputType := rawCons dom cod
  have left := exact_OpenCoverThinMatchingWindowInputs P.cover P.W P.V s body α Γ ctx inputType fn function
  have right := exact_OpenCoverThinMatchingWindowInputs P.cover P.W P.V s body α Γ ctx dom arg argument
  obtain ⟨sTypes⟩ := syntaxGuards
  obtain ⟨tTypes⟩ := typedGuards
  obtain ⟨fSyntax⟩ := left.valid
  obtain ⟨aSyntax⟩ := right.valid
  obtain ⟨fType⟩ := left.typed
  obtain ⟨aType⟩ := right.typed
  have children : Nonempty (Derivation body Γ (refinedAuxChildren V TV dom cod fn arg)) :=
    ⟨Derivation.conjunctionIntroduction sTypes (Derivation.conjunctionIntroduction fSyntax aSyntax)⟩
  have windows : Nonempty (Derivation body Γ (strictAuxChildren base S ctx dom cod fn arg)) :=
    ⟨Derivation.conjunctionIntroduction tTypes (Derivation.conjunctionIntroduction fType aType)⟩
  have valid := exact_OpenCoverRefinedAuxSyntaxIntro V TV body α Γ dom cod fn arg children
  have typed := exact_OpenCoverStrictAuxIntroduce base S body α Γ ctx dom cod fn arg windows
  have context := exact_OpenCoverThinMatchingContextTransport body α Γ ctx inputType fn cod key left.context
  exact exact_OpenCoverCombinedRestrictedWrapper V TV M M0 B T s body α Γ ctx cod key valid typed context

#print axioms exact_OpenCoverCombinedWrappedAuxFormation

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxProof
