module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSeedGrammarTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedSeedPresenceChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSeedGrammarProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm measurePair)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedRename)
open NumberedWindowInternalCoverSelectedGrammarWidthObservationProof (observationCases)
open NumberedWindowInternalCoverSelectedGrammarOptionOpenProof
  (exact_ObservedSelectedTerms exact_OpenSelectedGrammarFactoredScratch)
open NumberedWindowInternalSparsePackedSeedPresenceChecks (exact_SeedInGivenVertices)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalCoverSelectedSeedGrammarTargets

theorem seedGrammarRename {body : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)}
    (s : NumberedWindowScalarAlgorithm.Settings) (q d b state vertices args : OTerm α)
    (held : SeedGrammar s body Γ q d b state vertices args)
    (j : α → β) (Δ : List (Formula β)) (keep : ∀ p ∈ Γ, p.relabel j ∈ Δ) :
    SeedGrammar s body Δ (q.relabel j) (d.relabel j) (b.relabel j) (state.relabel j)
      (vertices.relabel j) (args.relabel j) := by
  have a := renameInto held.actual j Δ keep
  simp only [observedRename,headsTerm,typesTerm,numeralRename] at a
  have m := renameInto held.member j Δ keep
  rw [graphRename] at m
  exact ⟨a,m⟩

theorem exact_OpenCoverSelectedSeedGrammar : ExactOpenCoverSelectedSeedGrammar := by
  intro V N X W s body α Γ ctx ty q x m d b goal least valid measured pair next
  let C := selectedCover V N
  apply observationCases d (headsTerm s α) (typesTerm s α) b goal
  intro β j Δ state vertices args keep scope
  simp only [headsTerm,typesTerm,numeralRename] at scope
  have l := renameInto least j Δ keep
  rw [leastRename] at l
  have v := renameInto valid j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at v
  have r := renameInto measured j Δ keep
  rw [unaryRename] at r
  have p := renameInto pair j Δ keep
  simp only [measurePair,programRename,binaryInputsRename] at p
  have terms := exact_ObservedSelectedTerms (d.relabel j) (headsTerm s β) (typesTerm s β)
    (b.relabel j) state vertices args scope
  have cv := (exact_OpenSelectedGrammarFactoredScratch V N s (m.relabel j) (d.relabel j) (b.relabel j)
    vertices (q.relabel j) v r p terms).2
  obtain ⟨rule⟩ := exact_SeedInGivenVertices C X W s body β Δ
    (ctx.relabel j) (ty.relabel j) (q.relabel j) (x.relabel j) vertices
  obtain ⟨l⟩ := l
  obtain ⟨cv⟩ := cv
  exact next β j Δ state vertices args keep
    ⟨scope,⟨Derivation.implicationElimination rule (Derivation.conjunctionIntroduction l cv)⟩⟩

#print axioms seedGrammarRename
#print axioms exact_OpenCoverSelectedSeedGrammar
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSeedGrammarProof
