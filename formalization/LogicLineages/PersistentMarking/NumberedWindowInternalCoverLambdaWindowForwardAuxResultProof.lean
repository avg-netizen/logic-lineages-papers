module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaAuxBodyOwnTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowResultTypeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTransportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaWindowForwardAuxResultProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeWindow)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (precedingBase lambdaLexicalWindow)
open NumberedWindowInternalStrictAuxWindowResultTypeProof (exact_OpenStrictAuxWindowResultType)
open NumberedWindowInternalCoverRefinedInductionDispatchTransportProof (moveWindowType)
open NumberedWindowInternalCoverStrictAuxForwardProof (exact_OpenCoverLambdaWindowForwardAuxLayer)
open NumberedWindowInternalCoverLambdaAuxBodyOwnTargets

theorem exact_OpenCoverLambdaWindowForwardAuxResult : ExactOpenCoverLambdaWindowForwardAuxResult := by
  intro s B T body α Γ ctx dom cod fp ap result fnLam fnAux argLam argAux actual
  let P := precedingBase s B
  let S := refitGuard s T
  let key := auxiliaryTerm dom cod (suc fp) (suc ap)
  obtain ⟨equalType⟩ := exact_OpenStrictAuxWindowResultType P S body α Γ ctx result dom cod
    (suc fp) (suc ap) actual
  have oldAtCod := moveWindowType (numberedTypeWindow s B T) ctx result cod key equalType actual
  have newAtCod := exact_OpenCoverLambdaWindowForwardAuxLayer s B T body α Γ ctx dom cod fp ap
    fnLam fnAux argLam argAux oldAtCod
  exact moveWindowType (lambdaLexicalWindow s B T) ctx cod result key (symm equalType) newAtCod

#print axioms exact_OpenCoverLambdaWindowForwardAuxResult

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaWindowForwardAuxResultProof
