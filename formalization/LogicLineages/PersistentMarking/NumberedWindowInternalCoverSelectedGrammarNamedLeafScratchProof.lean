module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNamedLeafTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNamedLeafStageProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenDataProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNamedLeafScratchProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (valueUnique headTransport programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open ID1Completion.InternalOriginalOrderSyntaxProof (orderRename)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverNamedLeavesOpenDataProof (namedRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm measurePair)
open NumberedWindowInternalCoverSelectedGrammarWidthObservationProof (observationCases)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverSelectedGrammarOptionOpenProof
  (exact_ObservedSelectedTerms exact_OpenSelectedGrammarFactoredScratch)
open NumberedWindowInternalCoverSelectedGrammarNamedLeafTargets
open NumberedWindowInternalCoverSelectedGrammarNamedLeafStageProof (exact_OpenSelectedGrammarNamedLeafAtSuccessor)

attribute [local irreducible] programGraph

theorem exact_OpenSelectedGrammarNamedLeafScratch : ExactOpenSelectedGrammarNamedLeafScratch := by
  intro b V Measure s body α Γ m d M vertices ty i ht hi valid measured pair held
  apply observationCases (suc d) (headsTerm s α) (typesTerm s α) M _
  intro β j Δ next out args keep after
  rw [graphRename,namedRename]
  simp only [headsTerm,typesTerm,sucRelabel,numeralRename] at after
  have ht' := renameInto ht j Δ keep
  have hi' := renameInto hi j Δ keep
  simp only [orderRename,sucRelabel] at hi'
  have valid' := renameInto valid j Δ keep
  have measured' := renameInto measured j Δ keep
  have pair' := renameInto pair j Δ keep
  have held' := renameInto held j Δ keep
  simp only [graphRename,typesTerm,numeralRename] at ht'
  simp only [unaryRename,namedRename,sucRelabel,zRelabel] at valid'
  simp only [unaryRename,namedRename] at measured' held'
  simp only [measurePair,programRename,binaryInputsRename,sucRelabel] at pair'
  let H := headsTerm s β
  let K := typesTerm s β
  let key := namedTerm b.toNat (ty.relabel j) (i.relabel j)
  have hit := exact_OpenSelectedGrammarNamedLeafAtSuccessor b body β Δ
    (d.relabel j) H K (M.relabel j) next out args (ty.relabel j) (i.relabel j) after ht' hi'
  have terms := exact_ObservedSelectedTerms (suc (d.relabel j)) H K (M.relabel j) next out args after
  have installed := exact_OpenSelectedGrammarFactoredScratch V Measure s (m.relabel j)
    (suc (d.relabel j)) (M.relabel j) out key valid' measured' pair' terms
  let P := scratchVertices (selectedCover V Measure) s
  have eq := valueUnique P out (vertices.relabel j) ![key] installed.2 held'
  exact headTransport scratchMember (suc z) out (vertices.relabel j) ![key] eq hit

#print axioms exact_OpenSelectedGrammarNamedLeafScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNamedLeafScratchProof
