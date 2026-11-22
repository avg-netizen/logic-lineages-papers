module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentInductionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentInductionLocalProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentInductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaWindowForwardNonRecursiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowResultTypeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentInductionStepProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeWindow)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (precedingBase lambdaLexicalBase lambdaLexicalWindow)
open NumberedWindowInternalCoverLambdaWindowForwardNonRecursiveProof (exact_OpenCoverLambdaWindowForwardNonRecursive)
open NumberedWindowInternalCoverStrictAuxForwardProof (exact_OpenCoverStrictAuxForward)
open NumberedWindowInternalStrictAuxWindowResultTypeProof (exact_OpenStrictAuxWindowResultType)
open NumberedWindowInternalCoverRefinedInductionDispatchTransportProof (moveWindowType)
open NumberedWindowInternalCoverAuxFragmentGuardTargets (fragmentGuard)
open NumberedWindowInternalCoverAuxFragmentCasesProof (exact_OpenCoverAuxFragmentCases)
open NumberedWindowInternalCoverAuxFragmentInductionSyntaxTargets
open NumberedWindowInternalCoverAuxFragmentInductionSyntaxProof (forwardBelowRename)
open NumberedWindowInternalCoverAuxFragmentInductionLocalProof (moveForwardWindowKey actualBelowChildForward)
open NumberedWindowInternalCoverAuxFragmentInductionTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem atAuxKey (s : Settings) (B : Program 2) (T : Program 1)
    (ctx raw result dom cod fn arg : OTerm α)
    (pack : Nonempty (Derivation body Γ (eqn raw (auxiliaryTerm dom cod fn arg))))
    (fnSmall : Nonempty (Derivation body Γ (ltF fn raw)))
    (argSmall : Nonempty (Derivation body Γ (ltF arg raw)))
    (fnAccepted : Nonempty (Derivation body Γ (unary fragmentGuard (suc z) fn)))
    (argAccepted : Nonempty (Derivation body Γ (unary fragmentGuard (suc z) arg)))
    (below : Nonempty (Derivation body Γ
      (forwardBelow (numberedTypeWindow s B T) (lambdaLexicalWindow s B T) ctx raw)))
    (old : Nonempty (Derivation body Γ (windowAt (numberedTypeWindow s B T) ctx result raw))) :
    Nonempty (Derivation body Γ (windowAt (lambdaLexicalWindow s B T) ctx result raw)) := by
  let P := numberedTypeWindow s B T
  let Q := lambdaLexicalWindow s B T
  let base := precedingBase s B
  let target := precedingBase s (lambdaLexicalBase s B T)
  let guard := refitGuard s T
  let key := auxiliaryTerm dom cod fn arg
  have before := moveForwardWindowKey P ctx result raw key pack old
  obtain ⟨sameType⟩ := exact_OpenStrictAuxWindowResultType base guard body α Γ ctx result dom cod fn arg before
  have atCod := moveWindowType P ctx result cod key sameType before
  have atFn := actualBelowChildForward P Q ctx raw fn (rawCons dom cod) below fnSmall fnAccepted
  have atArg := actualBelowChildForward P Q ctx raw arg dom below argSmall argAccepted
  have afterCod := exact_OpenCoverStrictAuxForward base target guard body α Γ ctx dom cod fn arg atFn atArg atCod
  have after := moveWindowType Q ctx cod result key (symm sameType) afterCod
  obtain ⟨sameKey⟩ := pack
  exact moveForwardWindowKey Q ctx result key raw ⟨symm sameKey⟩ after

theorem exact_OpenCoverAuxFragmentInductionStep : ExactOpenCoverAuxFragmentInductionStep := by
  intro s B T body α Γ ctx raw result earlier accepted old
  let P := numberedTypeWindow s B T
  let Q := lambdaLexicalWindow s B T
  let goal : Formula α := windowAt Q ctx result raw
  apply exact_OpenCoverAuxFragmentCases body α Γ raw goal accepted
  · intro β j Δ prior keep eq noLambda noAux
    let c := ctx.relabel j
    let r := result.relabel j
    let q := raw.relabel j
    have before := renameInto old j Δ keep
    rw [windowRename] at before
    have oldAtSucc := moveForwardWindowKey P c r q (suc prior) eq before
    have typed := exact_OpenCoverLambdaWindowForwardNonRecursive s B T body β Δ c prior r noLambda noAux oldAtSucc
    obtain ⟨eq⟩ := eq
    rw [goal,windowRename]
    exact moveForwardWindowKey Q c r (suc prior) q ⟨symm eq⟩ typed
  · intro β j Δ dom cod fn arg keep _ packing fnSmall argSmall fnAccepted argAccepted
    have h := renameInto earlier j Δ keep
    rw [forwardBelowRename] at h
    have before := renameInto old j Δ keep
    rw [windowRename] at before
    rw [goal,windowRename]
    exact atAuxKey s B T (ctx.relabel j) (raw.relabel j) (result.relabel j) dom cod fn arg
      packing fnSmall argSmall fnAccepted argAccepted h before

#print axioms exact_OpenCoverAuxFragmentInductionStep

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentInductionStepProof
