module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedBaseTapeForwardTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedBaseTapeForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalGraphForwardBasicsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedMemoStepSelectionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverInstallNonAuxWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaWindowForwardNonRecursiveProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim)
open ID1Completion.InternalControlGraphSupportProof (projectionValue successorValue programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalAuxExchangeMemoStepTargets (binaryAfter currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph)
open NumberedWindowInternalAuxMeasureStepTargets (shapeCheck)
open NumberedWindowInternalAuxWindowOpenTargets (contextStep windowGraph)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow strictAuxUpdate strictAuxPositive)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (precedingBase lambdaLexicalBase lambdaLexicalWindow)
open NumberedWindowInternalCoverFittedMemoStepSelectionProof (exact_OpenSelectedFittedStepCases)
open NumberedWindowInternalCoverInstallNonAuxWindowProof (exact_OpenCoverInstallNonAuxWindow)
open NumberedWindowInternalCoverLocalGraphForwardBasicsProof (applyTape)
open NumberedWindowInternalCoverFittedBaseTapeForwardProof (exact_OpenCoverFittedBaseTapeForward)
open NumberedWindowInternalCoverFittedBaseTapeForwardTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem beforeStrictNonAux (A : Program 2) (T : Program 1)
    (ctx prior result old : OTerm α)
    (notAux : Nonempty (Derivation body Γ (unary termShape z (suc prior))))
    (actual : Nonempty (Derivation body Γ
      (contextStep (strictAuxUpdate A T) (suc result) prior old ctx))) :
    Nonempty (Derivation body Γ (programGraph A (suc result) ![ctx,suc prior])) := by
  let raw := suc prior
  let xs : Fin 4 → OTerm α := ![prior,old,ctx,z]
  have key : Nonempty (Derivation body Γ (programGraph currentKey raw xs)) :=
    unaryGraph .succ (.projection 0) raw prior xs (successorValue ![prior]) (projectionValue 0 xs)
  have noAux := unaryGraph termShape currentKey z raw xs notAux key
  have picked := zeroBranchElim shapeCheck (binaryAfter A (.projection 2) currentKey)
    (strictAuxPositive T) (suc result) xs noAux actual
  apply compositionRecover A ![.projection 2,currentKey] (suc result) xs ![ctx,raw] picked
  intro i
  exact Fin.cases (projectionValue 2 xs) (Fin.cases key (fun j => Fin.elim0 j)) i

private theorem atNonrecursiveStep (s : Settings) (B : Program 2) (T : Program 1)
    (ctx prior result old : OTerm α)
    (notLambda : Nonempty (Derivation body Γ (unary (header 2 2) z (suc prior))))
    (notAux : Nonempty (Derivation body Γ (unary termShape z (suc prior))))
    (actual : Nonempty (Derivation body Γ
      (contextStep (strictAuxUpdate (precedingBase s B) (refitGuard s T)) (suc result) prior old ctx))) :
    Nonempty (Derivation body Γ (windowGraph (lambdaLexicalWindow s B T) ctx result (suc prior))) := by
  let P := precedingBase s B
  let Q := precedingBase s (lambdaLexicalBase s B T)
  let S := refitGuard s T
  have before := beforeStrictNonAux P S ctx prior result old notAux actual
  have pq := exact_OpenCoverFittedBaseTapeForward s B T body α Γ ctx (suc prior) notLambda
  have after := applyTape P Q ![ctx,suc prior] (suc result) pq before
  exact exact_OpenCoverInstallNonAuxWindow Q S body α Γ ctx prior result notAux after

theorem exact_OpenCoverLambdaWindowForwardNonRecursive : ExactOpenCoverLambdaWindowForwardNonRecursive := by
  intro s B T body α Γ ctx prior result notLambda notAux actual
  let A : Program 2 := precedingBase s B
  let S : Program 1 := refitGuard s T
  let W : Program 3 := lambdaLexicalWindow s B T
  let Q : Formula α := windowGraph W ctx result (suc prior)
  apply exact_OpenSelectedFittedStepCases A S prior ctx result Q actual
  intro β j Δ old keep step
  have h := renameInto notLambda j Δ keep
  have a := renameInto notAux j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at h a
  simp only [Q,windowGraph,programRename,tripleInputsRename,sucRelabel,zRelabel]
  exact atNonrecursiveStep s B T (ctx.relabel j) (prior.relabel j) (result.relabel j) old h a step

#print axioms exact_OpenCoverLambdaWindowForwardNonRecursive

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaWindowForwardNonRecursiveProof
