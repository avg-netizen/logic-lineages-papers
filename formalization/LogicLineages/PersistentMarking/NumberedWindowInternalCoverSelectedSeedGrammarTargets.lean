module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineOpenTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSeedGrammarTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseCoverScratch (coverOption scratchVertices)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)

structure SeedGrammar (s : Settings) (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (q d b state vertices args : OTerm α) : Prop where
  actual : Nonempty (Derivation body Γ (observed d (headsTerm s α) (typesTerm s α) b state vertices args))
  member : Nonempty (Derivation body Γ (memberGraph vertices q))

/-- The successful least is about the actual raw seed. The supplied
selected measurement and pair are actual graph reports at that seed.
The chosen original grammar is observed at exactly those coordinates. -/
def ExactOpenCoverSelectedSeedGrammar : Prop :=
  ∀ (V N : Program 1) (X : Program 2) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx ty q x m d b : OTerm α) (goal : Formula α),
    Nonempty (Derivation body Γ (leastGraph (selectedCover V N) X W s ctx ty q x)) →
    Nonempty (Derivation body Γ (unary V (suc z) q)) →
    Nonempty (Derivation body Γ (unary N m q)) →
    Nonempty (Derivation body Γ (codePair m d b)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (state vertices args : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      SeedGrammar s body Δ (q.relabel j) (d.relabel j) (b.relabel j) state vertices args →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSeedGrammarTargets
