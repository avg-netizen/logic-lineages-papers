module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPositiveLengthTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPositiveLengthProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedLengthReachPackedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPositiveLengthReachProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename tripleInputsRename)
open NumberedWindowInternalSparseScalarEdge (edgeGraph)
open NumberedWindowInternalSparseDirectedSeen (edgeTape)
open NumberedWindowInternalCoverCombinedRestrictedPositiveLengthProof (exact_OpenCoverPositiveScratchLength)
open NumberedWindowInternalCoverCombinedRestrictedLengthReachPackedProof (exact_OpenCoverPackedLengthReach)
open NumberedWindowInternalCoverCombinedRestrictedPositiveLengthTargets

attribute [local irreducible] programGraph

theorem exact_OpenCoverCombinedRestrictedPairedReach : ExactOpenCoverCombinedRestrictedPairedReach := by
  intro V TV M M0 B T base s body α Γ ctx dom cod f g arg vertices pool P W X a b both edge actual
  apply exact_OpenCoverPositiveScratchLength body α Γ vertices a (memberGraph pool b) both.memberA
  intro β j Δ fuel keep length
  rw [graphRename]
  have scratch := renameInto both.scratchA j Δ keep
  have ma := renameInto both.memberA j Δ keep
  have mb := renameInto both.memberB j Δ keep
  have arc := renameInto edge j Δ keep
  have computed := renameInto actual j Δ keep
  rw [unaryRename] at scratch
  rw [graphRename] at ma mb
  simp only [edgeGraph,programRename,edgeTape,quadInputsRename,sucRelabel,zRelabel] at arc
  simp only [programRename,tripleInputsRename] at computed
  exact exact_OpenCoverPackedLengthReach P.cover X W s body β Δ (ctx.relabel j) (cod.relabel j)
    (vertices.relabel j) (a.relabel j) (b.relabel j) fuel (pool.relabel j)
    scratch length ma mb arc computed

#print axioms exact_OpenCoverCombinedRestrictedPairedReach
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPositiveLengthReachProof
