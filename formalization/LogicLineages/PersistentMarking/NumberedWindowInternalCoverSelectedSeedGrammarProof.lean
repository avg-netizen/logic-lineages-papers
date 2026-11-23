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
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
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
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)

attribute [local irreducible] programGraph

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

private theorem seedMember {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty q x vertices : OTerm α)
    (least : Nonempty (Derivation body Γ (leastGraph C X W s ctx ty q x)))
    (cv : Nonempty (Derivation body Γ (unary (scratchVertices C s) vertices q))) :
    Nonempty (Derivation body Γ (memberGraph vertices q)) := by
  obtain ⟨rule⟩ := exact_SeedInGivenVertices C X W s body α Γ ctx ty q x vertices
  obtain ⟨l⟩ := least
  obtain ⟨cv⟩ := cv
  exact ⟨Derivation.implicationElimination rule (Derivation.conjunctionIntroduction l cv)⟩

private theorem selectedScratch {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (V N : Program 1) (s : Settings) (q m d b state vertices args : OTerm α)
    (valid : Nonempty (Derivation body Γ (unary V (suc z) q)))
    (measured : Nonempty (Derivation body Γ (unary N m q)))
    (pair : Nonempty (Derivation body Γ (codePair m d b)))
    (scope : Nonempty (Derivation body Γ (observed d (headsTerm s α) (typesTerm s α)
      b state vertices args))) :
    Nonempty (Derivation body Γ (unary (scratchVertices (selectedCover V N) s) vertices q)) := by
  have terms := exact_ObservedSelectedTerms d (headsTerm s α) (typesTerm s α) b state vertices args scope
  exact (exact_OpenSelectedGrammarFactoredScratch V N s m d b vertices q valid measured pair terms).2

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
  simp only [codePair,programRename,binaryInputsRename] at p
  have cv := selectedScratch V N s (q.relabel j) (m.relabel j) (d.relabel j)
    (b.relabel j) state vertices args v r p scope
  have hit := seedMember C X W s (ctx.relabel j) (ty.relabel j) (q.relabel j) (x.relabel j) vertices l cv
  exact next β j Δ state vertices args keep ⟨scope,hit⟩

#print axioms seedGrammarRename
#print axioms exact_OpenCoverSelectedSeedGrammar
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSeedGrammarProof
