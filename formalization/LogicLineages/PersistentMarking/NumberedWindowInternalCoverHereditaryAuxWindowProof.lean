module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHereditaryAuxTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaWindowForwardNonRecursiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowResultTypeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTransportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverHereditaryAuxWindowProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeWindow)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (precedingBase lambdaLexicalBase lambdaLexicalWindow)
open NumberedWindowInternalStrictAuxWindowResultTypeProof (exact_OpenStrictAuxWindowResultType)
open NumberedWindowInternalCoverRefinedInductionDispatchTransportProof (moveWindowType)
open NumberedWindowInternalCoverStrictAuxForwardProof (exact_OpenCoverStrictAuxForward)
open NumberedWindowInternalCoverLambdaWindowForwardNonRecursiveProof
  (exact_OpenCoverLambdaWindowForwardNonRecursive)
open NumberedWindowInternalCoverHereditaryAuxTargets

theorem exact_OpenCoverHereditaryAuxWindowForward : ExactOpenCoverHereditaryAuxWindowForward := by
  intro s B T body α Γ ctx raw tree
  let P := precedingBase s B
  let Q := precedingBase s (lambdaLexicalBase s B T)
  let R := refitGuard s T
  induction tree with
  | terminal prior noLambda noAux =>
    intro result
    exact exact_OpenCoverLambdaWindowForwardNonRecursive s B T body α Γ ctx prior result noLambda noAux
  | fork dom cod fn arg _ _ _ _ first second =>
    intro result actual
    let key := auxiliaryTerm dom cod fn arg
    obtain ⟨eq⟩ := exact_OpenStrictAuxWindowResultType P R body α Γ ctx result dom cod fn arg actual
    have before := moveWindowType (numberedTypeWindow s B T) ctx result cod key eq actual
    have after := exact_OpenCoverStrictAuxForward P Q R body α Γ ctx dom cod fn arg
      (first (rawCons dom cod)) (second dom) before
    exact moveWindowType (lambdaLexicalWindow s B T) ctx cod result key (symm eq) after

#print axioms exact_OpenCoverHereditaryAuxWindowForward

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverHereditaryAuxWindowProof
