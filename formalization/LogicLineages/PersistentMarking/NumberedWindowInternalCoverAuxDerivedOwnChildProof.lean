module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxDerivedOwnTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaDerivedOwnInputSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureAlignProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxDerivedOwnChildProof
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
open NumberedWindowInternalCoverSelectedGrammarOptionOpenProof
  (exact_ObservedSelectedTerms exact_OpenSelectedGrammarFactoredScratch)
open NumberedWindowInternalCoverSelectedGrammarWidthObservationProof (observationCases)
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedRename)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredTargets (chosenMeasure MeasuredChild)
open NumberedWindowInternalCoverLambdaDerivedOwnInputSyntaxProof (ihRename specializeIH)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntax)
open NumberedWindowInternalChosenAuxMeasureAlignProof (moveChild)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (measureRename pairRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverAuxDerivedOwnTargets

variable {body : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)} {Δ : List (Formula β)}

theorem moveLocal (V TV M : Program 1) (W : Program 3) (s : Settings)
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) {ctx ty q : OTerm α}
    (child : LocalChild V TV M W s body Γ ctx ty q) :
    LocalChild V TV M W s body Δ (ctx.relabel j) (ty.relabel j) (q.relabel j) := by
  have valid := renameInto child.valid j Δ keep
  have typed := renameInto child.typed j Δ keep
  have ih := renameInto child.ih j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at valid
  rw [windowRename] at typed
  rw [ihRename] at ih
  exact ⟨valid,typed,ih⟩

theorem moveMeasured (M : Program 1) (s : Settings)
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    {m d width state terms args q : OTerm α}
    (child : MeasuredChild M s body Γ m d width state terms args q) :
    MeasuredChild M s body Δ (m.relabel j) (d.relabel j) (width.relabel j)
      (state.relabel j) (terms.relabel j) (args.relabel j) (q.relabel j) := by
  have measured := renameInto child.measurement j Δ keep
  have code := renameInto child.code j Δ keep
  have gram := renameInto child.grammar j Δ keep
  have occurs := renameInto child.occurs j Δ keep
  rw [measureRename] at measured
  rw [pairRename] at code
  simp only [observedRename,headsTerm,typesTerm,numeralRename] at gram
  rw [graphRename] at occurs
  exact ⟨measured,code,gram,occurs⟩

theorem exact_OpenCoverAuxMeasuredChild : ExactOpenCoverAuxMeasuredChild := by
  intro V TV M W s body α Γ ctx ty q m d width state terms args localData actual gram
  have view := exact_ObservedSelectedTerms d (headsTerm s α) (typesTerm s α) width state terms args gram
  have installed := exact_OpenSelectedGrammarFactoredScratch (auxSyntax V TV) (chosenMeasure M) s
    m d width terms q localData.valid actual.observed actual.coords view
  obtain ⟨scratch⟩ := installed.2
  obtain ⟨typed⟩ := localData.typed
  obtain ⟨rule⟩ := specializeIH W (auxCover V TV M) s ctx ty q terms localData.ih
  have hit := Derivation.implicationElimination (Derivation.implicationElimination rule typed) scratch
  exact ⟨actual.observed,actual.coords,gram,⟨hit⟩⟩

theorem exact_OpenCoverAuxMeasuredChildCases : ExactOpenCoverAuxMeasuredChildCases := by
  intro V TV M W s body α Γ ctx ty q m d width goal localData actual next
  apply observationCases d (headsTerm s α) (typesTerm s α) width goal
  intro β j Δ state terms args keep gram
  simp only [headsTerm,typesTerm,numeralRename] at gram
  have local' := moveLocal V TV M W s j keep localData
  have actual' := moveChild M j Δ keep actual
  exact next β j Δ state terms args keep (exact_OpenCoverAuxMeasuredChild V TV M W s body β Δ
    (ctx.relabel j) (ty.relabel j) (q.relabel j) (m.relabel j) (d.relabel j) (width.relabel j)
    state terms args local' actual' gram)

#print axioms exact_OpenCoverAuxMeasuredChild
#print axioms exact_OpenCoverAuxMeasuredChildCases

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxDerivedOwnChildProof
