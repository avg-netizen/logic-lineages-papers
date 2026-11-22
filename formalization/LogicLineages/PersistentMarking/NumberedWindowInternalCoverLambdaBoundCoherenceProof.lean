module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundCoherenceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundOriginalBaseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundBaseRebuildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverInstallNonAuxWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafGrammarWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedResultWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalBoundWindowSelectedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundCoherenceProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel eqnRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverNamedLeavesOpenDataProof (namedRename)
open NumberedWindowInternalCoverNamedLeafIntrinsicShapeProof (exact_OpenCoverNamedLeafIntrinsicShape)
open NumberedWindowInternalCoverNamedLeafMeasureTargets (namedPrior)
open NumberedWindowInternalCoverHeadWindowTargets (grammarHeadBase)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeBase)
open NumberedWindowInternalCoverNamedResultTargets (namedResultBase)
open NumberedWindowInternalCoverLexicalBoundWindowTargets (lexicalBoundBase)
open NumberedWindowInternalCoverNamedLeafGrammarWindowProof (exact_OpenCoverNamedLeafGrammarWindowK)
open NumberedWindowInternalCoverLexicalBoundWindowSelectedProof (exact_OpenCoverLexicalBoundWindowSlot)
open NumberedWindowInternalCoverNamedResultWindowProof (exact_OpenCoverNamedResultWindow)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalCoverMeasuredDispatchRenameProof (moveStoredK)
open NumberedWindowInternalCoverLambdaBoundOriginalBaseProof (exact_OpenBoundOriginalBaseCases)
open NumberedWindowInternalCoverLambdaBoundBaseRebuildProof (rebuildSelectedBoundBase)
open NumberedWindowInternalCoverInstallNonAuxWindowProof (exact_OpenCoverInstallNonAuxWindow)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets
open NumberedWindowInternalCoverLambdaBoundCoherenceTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem goalRename (W : Program 3) (ctx ty i res : OTerm α) {β : Type} (j : α → β) :
    (windowGraph W ctx res (namedTerm 1 ty i)).relabel j =
      windowGraph W (ctx.relabel j) (res.relabel j) (namedTerm 1 (ty.relabel j) (i.relabel j)) := by
  simp only [windowGraph,programRename,tripleInputsRename,sucRelabel,zRelabel,namedRename]

theorem exact_OpenCoverLambdaBoundCoherence : ExactOpenCoverLambdaBoundCoherence := by
  intro s B T body α Γ ctx ty i result old
  let H := grammarHeadBase s (numberedTypeBase s B)
  let S := refitGuard s T
  let W := lambdaLexicalWindow s B T
  let Q := windowGraph W ctx result (namedTerm 1 ty i)
  have inK := exact_OpenCoverNamedLeafGrammarWindowK true s (lexicalBoundBase (namedResultBase H))
    S body α Γ ctx ty i result old
  have slot := exact_OpenCoverLexicalBoundWindowSlot s (namedResultBase H) S body α Γ ctx ty i result old
  have same := exact_OpenCoverNamedResultWindow true s H S body α Γ ctx ty i result old
  apply exact_OpenBoundOriginalBaseCases s B T ctx ty i result Q old
  intro β j Δ v keep original
  have fit := moveStoredK s j keep ty inK
  have slot' := renameInto slot j Δ keep
  simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at slot'
  have same' := renameInto same j Δ keep
  rw [eqnRelabel] at same'
  let c := ctx.relabel j
  let t := ty.relabel j
  let k := i.relabel j
  let r := result.relabel j
  let P := precedingBase s (lambdaLexicalBase s B T)
  have next := rebuildSelectedBoundBase s B T c t k r v original fit slot' same'
  have shape := exact_OpenCoverNamedLeafIntrinsicShape true body β Δ t k
  have actual : Nonempty (Derivation body Δ (windowGraph W c r (namedTerm 1 t k))) :=
    exact_OpenCoverInstallNonAuxWindow P S body β Δ c (namedPrior true t k) r shape.1 next
  let Want : Formula β → Prop := fun form => Nonempty (Derivation body Δ form)
  exact Eq.mpr (congrArg Want (goalRename W ctx ty i result j)) actual

#print axioms exact_OpenCoverLambdaBoundCoherence

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundCoherenceProof
