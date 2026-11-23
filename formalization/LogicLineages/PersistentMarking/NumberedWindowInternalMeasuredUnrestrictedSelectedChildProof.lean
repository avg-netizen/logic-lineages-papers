module

public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureParentTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureAlignProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedSelectedChildProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeast (poolAtSeed)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredTargets (MeasuredChild chosenMeasure)
open NumberedWindowInternalCoverSelectedGrammarWidthObservationProof (observationCases)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalChosenAuxMeasureParentTargets (AuxMeasureChild)
open NumberedWindowInternalChosenAuxMeasureAlignProof (moveChild)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (window syntaxWindow contextPresent ownSeed)
open NumberedWindowInternalMeasuredUnrestrictedWindowReportsProof (exact_OpenUnrestrictedWindowReports)
open NumberedWindowInternalCoverSelectedGrammarOptionOpenProof
  (exact_ObservedSelectedTerms exact_OpenSelectedGrammarFactoredScratch)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem ownFromWindow (C : Program 3) (s : Settings) (baseW : Program 3)
    (V : Program 1) (ctx ty child vertices : OTerm α)
    (held : Nonempty (Derivation B Γ (windowAt (window C s baseW V) ctx ty child)))
    (scratch : Nonempty (Derivation B Γ (unary (scratchVertices C s) vertices child))) :
    Nonempty (Derivation B Γ (memberGraph vertices child)) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,child]
  obtain ⟨outer⟩ := conjunctionRecover (syntaxWindow baseW V)
    (conjunction contextPresent (ownSeed C s)) xs held
  obtain ⟨bits⟩ := conjunctionRecover contextPresent (ownSeed C s) xs ⟨Derivation.conjunctionRight outer⟩
  apply compositionRecover scratchMember ![poolAtSeed C s,.projection 2] (suc z) xs ![vertices,child]
    ⟨Derivation.conjunctionRight bits⟩
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · apply compositionValue (scratchVertices C s) (fun _ : Fin 1 => .projection 2) vertices xs ![child] scratch
    intro k
    obtain rfl := Fin.eq_zero k
    exact projectionValue 2 xs
  · obtain rfl := Fin.eq_zero k
    exact projectionValue 2 xs

/-- The same selected grammar observation yields the actual measured
child occurrence, without a caller assumption of membership or a new
representative. The window's own bit is read at exactly this scratch. -/
theorem exact_OpenUnrestrictedSelectedChild (V baseM : Program 1) (s : Settings) (baseW : Program 3)
    (ctx ty child m d w state terms args : OTerm α) :
    let C := selectedCover V (chosenMeasure baseM)
    Nonempty (Derivation B Γ (windowAt (window C s baseW V) ctx ty child)) →
    AuxMeasureChild baseM B Γ child m d w →
    Nonempty (Derivation B Γ (observed d (headsTerm s α) (typesTerm s α) w state terms args)) →
    MeasuredChild baseM s B Γ m d w state terms args child := by
  intro C held measured scope
  obtain ⟨reports⟩ := exact_OpenUnrestrictedWindowReports C s baseW V ctx ty child held
  have term := exact_ObservedSelectedTerms d (headsTerm s α) (typesTerm s α) w state terms args scope
  have scratch := (exact_OpenSelectedGrammarFactoredScratch V (chosenMeasure baseM) s m d w terms child
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight reports)⟩ measured.observed measured.coords term).2
  exact ⟨measured.observed, measured.coords, scope, ownFromWindow C s baseW V ctx ty child terms held scratch⟩

/-- Genuinely choose the original observation at the measured child pair. -/
theorem exact_OpenUnrestrictedSelectedChildCases (V baseM : Program 1) (s : Settings) (baseW : Program 3)
    (ctx ty child m d w : OTerm α) (goal : Formula α)
    (held : Nonempty (Derivation B Γ
      (windowAt (window (selectedCover V (chosenMeasure baseM)) s baseW V) ctx ty child)))
    (measured : AuxMeasureChild baseM B Γ child m d w)
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (state terms args : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      MeasuredChild baseM s B Δ (m.relabel j) (d.relabel j) (w.relabel j) state terms args (child.relabel j) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  apply observationCases d (headsTerm s α) (typesTerm s α) w goal
  intro β j Δ state terms args keep scope
  simp only [headsTerm,typesTerm,numeralRename] at scope
  have window' := renameInto held j Δ keep
  rw [windowRename] at window'
  have measured' := moveChild baseM j Δ keep measured
  exact next β j Δ state terms args keep
    (exact_OpenUnrestrictedSelectedChild V baseM s baseW (ctx.relabel j) (ty.relabel j)
      (child.relabel j) (m.relabel j) (d.relabel j) (w.relabel j) state terms args window' measured' scope)

#print axioms exact_OpenUnrestrictedSelectedChild
#print axioms exact_OpenUnrestrictedSelectedChildCases
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedSelectedChildProof
