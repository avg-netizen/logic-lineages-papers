module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedOwnScratchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMeasureChildCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaDerivedOwnInputSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverChildOwnScopeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverSelectedGrammarOptionOpenProof
  (exact_ObservedSelectedTerms exact_OpenSelectedGrammarFactoredScratch)
open NumberedWindowInternalCoverSelectedGrammarWidthObservationProof (observationCases)
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedRename)
open NumberedWindowInternalCoverLambdaDerivedOwnInputSyntaxProof (ihRename specializeIH)
open NumberedWindowInternalCoverSharedMeasureChildCasesProof (moveMeasuredChild)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverSharedOwnScratchTargets

variable {body : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)} {Δ : List (Formula β)}

theorem moveLocal (V : Program 1) (R : Program 4) (W : Program 3) (s : Settings)
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) {ctx ty q : OTerm α}
    (child : ChildOwnInputs V R W s body Γ ctx ty q) :
    ChildOwnInputs V R W s body Δ (ctx.relabel j) (ty.relabel j) (q.relabel j) := by
  have valid := renameInto child.valid j Δ keep
  have typed := renameInto child.typed j Δ keep
  have ih := renameInto child.ih j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at valid
  rw [windowRename] at typed
  rw [ihRename] at ih
  exact ⟨valid,typed,ih⟩

theorem moveOwn (s : Settings) (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    {d b state terms args key : OTerm α} (child : OwnOccurrence s body Γ d b state terms args key) :
    OwnOccurrence s body Δ (d.relabel j) (b.relabel j) (state.relabel j) (terms.relabel j)
      (args.relabel j) (key.relabel j) := by
  have scope := renameInto child.observedScope j Δ keep
  simp only [observedRename,headsTerm,typesTerm,numeralRename] at scope
  have hit := renameInto child.ownKey j Δ keep
  rw [graphRename] at hit
  exact ⟨scope,hit⟩

theorem exact_OpenCoverChildOwnScopeCases : ExactOpenCoverChildOwnScopeCases := by
  intro V R W s body α Γ ctx ty q m d b goal localData actual next
  apply observationCases d (headsTerm s α) (typesTerm s α) b goal
  intro β j Δ state terms args keep gram
  simp only [headsTerm,typesTerm,numeralRename] at gram
  have local' := moveLocal V R W s j keep localData
  have actual' := moveMeasuredChild R j Δ keep actual
  let ctx' := ctx.relabel j
  let ty' := ty.relabel j
  let q' := q.relabel j
  let m' := m.relabel j
  let d' := d.relabel j
  let b' := b.relabel j
  let C := selectedCover V (selectedMeasure R)
  have view := exact_ObservedSelectedTerms d' (headsTerm s β) (typesTerm s β) b' state terms args gram
  have installed := exact_OpenSelectedGrammarFactoredScratch V (selectedMeasure R) s
    m' d' b' terms q' local'.valid actual'.selected actual'.coordinates view
  obtain ⟨scratch⟩ := installed.2
  obtain ⟨typed⟩ := local'.typed
  obtain ⟨rule⟩ := specializeIH W C s ctx' ty' q' terms local'.ih
  have hit := Derivation.implicationElimination (Derivation.implicationElimination rule typed) scratch
  exact next β j Δ state terms args keep ⟨gram,⟨hit⟩⟩

#print axioms exact_OpenCoverChildOwnScopeCases

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverChildOwnScopeProof
