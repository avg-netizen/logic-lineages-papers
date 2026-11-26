module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxForwardTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowParentProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxIntroduceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaWindowForwardNonRecursiveProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxForwardProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxChildren strictAuxWindow)
open NumberedWindowInternalStrictAuxWindowParentProof (exact_OpenStrictAuxWindowParent)
open NumberedWindowInternalCoverStrictAuxIntroduceProof (exact_OpenCoverStrictAuxIntroduce)
open NumberedWindowInternalCoverLambdaWindowForwardNonRecursiveProof
  (exact_OpenCoverLambdaWindowForwardNonRecursive)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (precedingBase lambdaLexicalBase)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalCoverStrictAuxForwardTargets

theorem exact_OpenCoverStrictAuxForward : ExactOpenCoverStrictAuxForward := by
  intro P Q T body α Γ ctx dom cod fn arg fnForward argForward actual
  rcases exact_OpenStrictAuxWindowParent P T body α Γ ctx dom cod fn arg actual with ⟨children⟩
  have types := Derivation.conjunctionLeft children
  have wins := Derivation.conjunctionRight children
  rcases fnForward ⟨Derivation.conjunctionLeft wins⟩ with ⟨fnNext⟩
  rcases argForward ⟨Derivation.conjunctionRight wins⟩ with ⟨argNext⟩
  have report : Nonempty (Derivation body Γ (strictAuxChildren Q T ctx dom cod fn arg)) :=
    ⟨Derivation.conjunctionIntroduction types (Derivation.conjunctionIntroduction fnNext argNext)⟩
  exact exact_OpenCoverStrictAuxIntroduce Q T body α Γ ctx dom cod fn arg report

theorem exact_OpenCoverLambdaWindowForwardAuxLayer : ExactOpenCoverLambdaWindowForwardAuxLayer := by
  intro s B T body α Γ ctx dom cod fp ap fnNoLam fnNoAux argNoLam argNoAux
  let P := precedingBase s B
  let Q := precedingBase s (lambdaLexicalBase s B T)
  let R := refitGuard s T
  have forwardFn : ChildWindowForward (strictAuxWindow P R) (strictAuxWindow Q R)
      body Γ ctx (rawCons dom cod) (suc fp) :=
    exact_OpenCoverLambdaWindowForwardNonRecursive s B T body α Γ ctx fp (rawCons dom cod) fnNoLam fnNoAux
  have forwardArg : ChildWindowForward (strictAuxWindow P R) (strictAuxWindow Q R)
      body Γ ctx dom (suc ap) :=
    exact_OpenCoverLambdaWindowForwardNonRecursive s B T body α Γ ctx ap dom argNoLam argNoAux
  exact exact_OpenCoverStrictAuxForward P Q R body α Γ ctx dom cod (suc fp) (suc ap) forwardFn forwardArg

#print axioms exact_OpenCoverStrictAuxForward
#print axioms exact_OpenCoverLambdaWindowForwardAuxLayer

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxForwardProof
