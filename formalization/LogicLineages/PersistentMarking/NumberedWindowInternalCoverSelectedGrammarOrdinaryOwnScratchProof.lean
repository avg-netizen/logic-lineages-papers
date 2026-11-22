module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnBoundsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnInputsRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnScratchProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (valueUnique headTransport)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalCoverSelectedGrammarWidthObservationProof (observationCases)
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedRename)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverSelectedGrammarOptionOpenProof
  (exact_ObservedSelectedTerms exact_OpenSelectedGrammarFactoredScratch)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTermPartProof (ordinaryRename)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnBoundsProof (exact_OpenSelectedGrammarOrdinaryAtBounds)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnInputsRenameProof (inputsRename)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem atSuccessor (V Measure : Program 1) (s : Settings)
    (m d M da Ma aState aTerms aArgs prev prevTerms prevArgs next out args vertices h a : OTerm α)
    (paid : OrdinaryOwnInputs V Measure s body Γ m d M da Ma aState aTerms aArgs h a)
    (before : Nonempty (Derivation body Γ (observed d (headsTerm s α) (typesTerm s α) M prev prevTerms prevArgs)))
    (after : Nonempty (Derivation body Γ (observed (suc d) (headsTerm s α) (typesTerm s α) M next out args)))
    (held : Nonempty (Derivation body Γ (unary (scratchVertices (selectedCover V Measure) s)
      vertices (ordinaryKey h a)))) :
    Nonempty (Derivation body Γ (memberGraph vertices (ordinaryKey h a))) := by
  let H := headsTerm s α
  let K := typesTerm s α
  let key := ordinaryKey h a
  have hit := exact_OpenSelectedGrammarOrdinaryAtBounds body α Γ d H K M da Ma aState aTerms aArgs
    prev prevTerms prevArgs next out args h a paid.argumentScope paid.argumentHit
    paid.argumentDepth paid.argumentWidth before after paid.headHit
  have terms := exact_ObservedSelectedTerms (suc d) H K M next out args after
  have installed := exact_OpenSelectedGrammarFactoredScratch V Measure s m (suc d) M out key
    paid.validity paid.measurement paid.parentPair terms
  let P := scratchVertices (selectedCover V Measure) s
  have eq := valueUnique P out vertices ![key] installed.2 held
  exact headTransport scratchMember (suc z) out vertices ![key] eq hit

private theorem withBefore (V Measure : Program 1) (s : Settings)
    (m d M da Ma aState aTerms aArgs prev prevTerms prevArgs vertices h a : OTerm α)
    (paid : OrdinaryOwnInputs V Measure s body Γ m d M da Ma aState aTerms aArgs h a)
    (before : Nonempty (Derivation body Γ (observed d (headsTerm s α) (typesTerm s α) M prev prevTerms prevArgs)))
    (held : Nonempty (Derivation body Γ (unary (scratchVertices (selectedCover V Measure) s)
      vertices (ordinaryKey h a)))) :
    Nonempty (Derivation body Γ (memberGraph vertices (ordinaryKey h a))) := by
  apply observationCases (suc d) (headsTerm s α) (typesTerm s α) M _
  intro β j Δ next out args keep after
  rw [graphRename,ordinaryRename]
  simp only [headsTerm,typesTerm,sucRelabel,numeralRename] at after
  have p := inputsRename V Measure s m d M da Ma aState aTerms aArgs h a j keep paid
  have before' := renameInto before j Δ keep
  simp only [observedRename,headsTerm,typesTerm,numeralRename] at before'
  have held' := renameInto held j Δ keep
  rw [unaryRename,ordinaryRename] at held'
  exact atSuccessor V Measure s (m.relabel j) (d.relabel j) (M.relabel j) (da.relabel j) (Ma.relabel j)
    (aState.relabel j) (aTerms.relabel j) (aArgs.relabel j)
    (prev.relabel j) (prevTerms.relabel j) (prevArgs.relabel j)
    next out args (vertices.relabel j) (h.relabel j) (a.relabel j) p before' after held'

theorem exact_OpenSelectedGrammarOrdinaryScratch : ExactOpenSelectedGrammarOrdinaryScratch := by
  intro V Measure s body α Γ m d M da Ma aState aTerms aArgs vertices h a paid held
  apply observationCases d (headsTerm s α) (typesTerm s α) M _
  intro β j Δ prev prevTerms prevArgs keep before
  rw [graphRename,ordinaryRename]
  simp only [headsTerm,typesTerm,numeralRename] at before
  have p := inputsRename V Measure s m d M da Ma aState aTerms aArgs h a j keep paid
  have held' := renameInto held j Δ keep
  rw [unaryRename,ordinaryRename] at held'
  exact withBefore V Measure s (m.relabel j) (d.relabel j) (M.relabel j) (da.relabel j) (Ma.relabel j)
    (aState.relabel j) (aTerms.relabel j) (aArgs.relabel j)
    prev prevTerms prevArgs (vertices.relabel j) (h.relabel j) (a.relabel j) p before held'

#print axioms exact_OpenSelectedGrammarOrdinaryScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnScratchProof
