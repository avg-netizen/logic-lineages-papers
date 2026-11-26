module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumberedOwnTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumberedOwnBoundsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumberedOwnInputsRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumberedOwnScratchProof
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
open NumberedWindowInternalCoverSelectedGrammarNumberedOwnTargets
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalCoverNumberedLayerOpenDataProof (numberedRename)
open NumberedWindowInternalCoverSelectedGrammarNumberedOwnBoundsProof (exact_OpenSelectedGrammarNumberedAtBounds)
open NumberedWindowInternalCoverSelectedGrammarNumberedOwnInputsRenameProof (inputsRename)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem atSuccessor (V Measure : Program 1) (s : Settings)
    (m d M dl Ml lState lTerms lArgs dr Mr rState rTerms rArgs prev prevTerms prevArgs next out args vertices h ty k l r : OTerm α)
    (paid : NumberedOwnInputs V Measure s body Γ m d M dl Ml lState lTerms lArgs dr Mr rState rTerms rArgs h ty k l r)
    (before : Nonempty (Derivation body Γ (observed d (headsTerm s α) (typesTerm s α) M prev prevTerms prevArgs)))
    (after : Nonempty (Derivation body Γ (observed (suc d) (headsTerm s α) (typesTerm s α) M next out args)))
    (held : Nonempty (Derivation body Γ (unary (scratchVertices (selectedCover V Measure) s)
      vertices (numberedTerm h ty k l r)))) :
    Nonempty (Derivation body Γ (memberGraph vertices (numberedTerm h ty k l r))) := by
  let H := headsTerm s α
  let K := typesTerm s α
  let key := numberedTerm h ty k l r
  have hit := exact_OpenSelectedGrammarNumberedAtBounds body α Γ d H K M dl Ml lState lTerms lArgs dr Mr rState rTerms rArgs
    prev prevTerms prevArgs next out args h ty k l r paid.prefix paid.suffix
    before after paid.headHit paid.typeHit paid.idBound
  have terms := exact_ObservedSelectedTerms (suc d) H K M next out args after
  have installed := exact_OpenSelectedGrammarFactoredScratch V Measure s m (suc d) M out key
    paid.validity paid.measurement paid.parentPair terms
  let P := scratchVertices (selectedCover V Measure) s
  have eq := valueUnique P out vertices ![key] installed.2 held
  exact headTransport scratchMember (suc z) out vertices ![key] eq hit

private theorem withBefore (V Measure : Program 1) (s : Settings)
    (m d M dl Ml lState lTerms lArgs dr Mr rState rTerms rArgs prev prevTerms prevArgs vertices h ty k l r : OTerm α)
    (paid : NumberedOwnInputs V Measure s body Γ m d M dl Ml lState lTerms lArgs dr Mr rState rTerms rArgs h ty k l r)
    (before : Nonempty (Derivation body Γ (observed d (headsTerm s α) (typesTerm s α) M prev prevTerms prevArgs)))
    (held : Nonempty (Derivation body Γ (unary (scratchVertices (selectedCover V Measure) s)
      vertices (numberedTerm h ty k l r)))) :
    Nonempty (Derivation body Γ (memberGraph vertices (numberedTerm h ty k l r))) := by
  apply observationCases (suc d) (headsTerm s α) (typesTerm s α) M _
  intro β j Δ next out args keep after
  rw [graphRename,numberedRename]
  simp only [headsTerm,typesTerm,sucRelabel,numeralRename] at after
  have p := inputsRename V Measure s m d M dl Ml lState lTerms lArgs dr Mr rState rTerms rArgs h ty k l r j keep paid
  have before' := renameInto before j Δ keep
  simp only [observedRename,headsTerm,typesTerm,numeralRename] at before'
  have held' := renameInto held j Δ keep
  rw [unaryRename,numberedRename] at held'
  exact atSuccessor V Measure s (m.relabel j) (d.relabel j) (M.relabel j) (dl.relabel j) (Ml.relabel j)
    (lState.relabel j) (lTerms.relabel j) (lArgs.relabel j) (dr.relabel j) (Mr.relabel j)
    (rState.relabel j) (rTerms.relabel j) (rArgs.relabel j)
    (prev.relabel j) (prevTerms.relabel j) (prevArgs.relabel j)
    next out args (vertices.relabel j) (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j) p before' after held'

theorem exact_OpenSelectedGrammarNumberedScratch : ExactOpenSelectedGrammarNumberedScratch := by
  intro V Measure s body α Γ m d M dl Ml lState lTerms lArgs dr Mr rState rTerms rArgs vertices h ty k l r paid held
  apply observationCases d (headsTerm s α) (typesTerm s α) M _
  intro β j Δ prev prevTerms prevArgs keep before
  rw [graphRename,numberedRename]
  simp only [headsTerm,typesTerm,numeralRename] at before
  have p := inputsRename V Measure s m d M dl Ml lState lTerms lArgs dr Mr rState rTerms rArgs h ty k l r j keep paid
  have held' := renameInto held j Δ keep
  rw [unaryRename,numberedRename] at held'
  exact withBefore V Measure s (m.relabel j) (d.relabel j) (M.relabel j) (dl.relabel j) (Ml.relabel j)
    (lState.relabel j) (lTerms.relabel j) (lArgs.relabel j) (dr.relabel j) (Mr.relabel j)
    (rState.relabel j) (rTerms.relabel j) (rArgs.relabel j)
    prev prevTerms prevArgs (vertices.relabel j) (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j) p before held'

#print axioms exact_OpenSelectedGrammarNumberedScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumberedOwnScratchProof
