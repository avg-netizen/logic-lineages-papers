module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarTypeLeafTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarTypeLeafStageProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarTypeLeafScratchProof
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
open NumberedWindowInternalCoverTypeLeavesTargets (typeLeafTerm)
open NumberedWindowInternalCoverTypeLeavesOpenDataProof (termRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm measurePair)
open NumberedWindowInternalCoverSelectedGrammarWidthObservationProof (observationCases)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverSelectedGrammarOptionOpenProof
  (exact_ObservedSelectedTerms exact_OpenSelectedGrammarFactoredScratch)
open NumberedWindowInternalCoverSelectedGrammarTypeLeafTargets
open NumberedWindowInternalCoverSelectedGrammarTypeLeafStageProof (exact_OpenSelectedGrammarTypeLeafAtSuccessor)

attribute [local irreducible] programGraph

theorem exact_OpenSelectedGrammarTypeLeafScratch : ExactOpenSelectedGrammarTypeLeafScratch := by
  intro V Measure s body α Γ m d M vertices ty ht valid measured pair held
  apply observationCases (suc d) (headsTerm s α) (typesTerm s α) M _
  intro β j Δ next out args keep after
  rw [graphRename,termRename]
  simp only [headsTerm,typesTerm,sucRelabel,numeralRename] at after
  have ht' := renameInto ht j Δ keep
  have valid' := renameInto valid j Δ keep
  have measured' := renameInto measured j Δ keep
  have pair' := renameInto pair j Δ keep
  have held' := renameInto held j Δ keep
  simp only [graphRename,typesTerm,numeralRename] at ht'
  simp only [unaryRename,termRename,sucRelabel,zRelabel] at valid'
  simp only [unaryRename,termRename] at measured' held'
  simp only [measurePair,programRename,binaryInputsRename,sucRelabel] at pair'
  let H := headsTerm s β
  let K := typesTerm s β
  let key := typeLeafTerm (ty.relabel j)
  have hit := exact_OpenSelectedGrammarTypeLeafAtSuccessor body β Δ
    (d.relabel j) H K (M.relabel j) next out args (ty.relabel j) after ht'
  have terms := exact_ObservedSelectedTerms (suc (d.relabel j)) H K (M.relabel j) next out args after
  have installed := exact_OpenSelectedGrammarFactoredScratch V Measure s (m.relabel j)
    (suc (d.relabel j)) (M.relabel j) out key valid' measured' pair' terms
  let P := scratchVertices (selectedCover V Measure) s
  have eq := valueUnique P out (vertices.relabel j) ![key] installed.2 held'
  exact headTransport scratchMember (suc z) out (vertices.relabel j) ![key] eq hit

#print axioms exact_OpenSelectedGrammarTypeLeafScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarTypeLeafScratchProof
