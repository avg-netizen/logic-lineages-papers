module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedPreparedProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalAppendTwoPairsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedOriginCasesRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanRoutedHeadProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedPreparedCasesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalListCodecSupportProof (consGraphRename)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalCertifiedUnionStepProof (Pr SplitCases)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalOriginKeptSplitTargets (evidence piece)
open NumberedWindowInternalOriginScanInductionSyntaxProof (renamePools)
open NumberedWindowInternalProjectedCountInductionSyntaxProof (projectRename)
open NumberedWindowInternalOpenOriginScanRoutedHeadProof (loopRename)
open NumberedWindowInternalLiteralTypedPartitionProof (Typed)
open NumberedWindowInternalRawUnionFromEquivalentPartsProof (Cmp)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalCertifiedPreparedTargets
open NumberedWindowInternalCertifiedPreparedProof (exact_OriginalCertifiedPreparedAtAppends)
open NumberedWindowInternalAppendTwoPairsProof (exact_OriginalAppendTwoPairs)
open NumberedWindowInternalCertifiedOriginCasesRenameProof (exact_OriginalSplitCasesRelabel)

attribute [local irreducible] programGraph
variable {α β : Type} {Γ : List (Formula α)} {Δ : List (Formula β)}

private theorem relocate (i : Program 1) (r : Program 3) (c : Nat)
    {a b v l s t kept d dh dTail removed rawDL rawDR p fullRows rowsL rowsR pL pR pJoin oldJoin : OTerm α}
    {w : Fin 8 → OTerm α}
    (h : Known i r c Γ a b v l s t kept d dh dTail removed rawDL rawDR p fullRows rowsL rowsR pL pR pJoin oldJoin w)
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    Known i r c Δ (a.relabel j) (b.relabel j) (v.relabel j) (l.relabel j) (s.relabel j)
      (t.relabel j) (kept.relabel j) (d.relabel j) (dh.relabel j) (dTail.relabel j) (removed.relabel j)
      (rawDL.relabel j) (rawDR.relabel j) (p.relabel j) (fullRows.relabel j) (rowsL.relabel j)
      (rowsR.relabel j) (pL.relabel j) (pR.relabel j) (pJoin.relabel j) (oldJoin.relabel j)
      (fun u => (w u).relabel j) := by
  constructor
  · exact renameParser a l h.leftParse j Δ keep
  · exact renameParser b s h.rightParse j Δ keep
  · exact renameParser v t h.targetParse j Δ keep
  · simpa only [Typed,unaryRename,sucRelabel,zRelabel] using renameInto h.leftTyped j Δ keep
  · simpa only [Typed,unaryRename,sucRelabel,zRelabel] using renameInto h.rightTyped j Δ keep
  · simpa only [Typed,unaryRename,sucRelabel,zRelabel] using renameInto h.targetTyped j Δ keep
  · simpa only [consGraphRename] using renameInto h.removedCons j Δ keep
  · simpa only [evidence,piece,conjunctionRename,programRename,binaryInputsRename,sucRelabel,zRelabel] using
      renameInto h.allocation j Δ keep
  · exact renamePools h.pools j keep
  · simpa only [loopRename] using renameInto h.leftRows j Δ keep
  · simpa only [loopRename] using renameInto h.rightRows j Δ keep
  · simpa only [projectRename] using renameInto h.leftProj j Δ keep
  · simpa only [projectRename] using renameInto h.rightProj j Δ keep
  · exact renamePair append pJoin pL pR h.bothProjected j keep
  · simpa only [Cmp,sucRelabel,zRelabel] using renamePair permutation (suc z) p pJoin h.projectedCount j keep
  · exact renamePair append oldJoin kept p h.oldAppend j keep
  · simpa only [Cmp,sucRelabel,zRelabel] using renamePair permutation (suc z) t oldJoin h.oldCount j keep

theorem exact_OriginalCertifiedPreparedCases (i : Program 1) (r : Program 3) (c : Nat)
    (a b v l s t kept d dh dTail removed rawDL rawDR p fullRows rowsL rowsR pL pR pJoin oldJoin : OTerm α)
    (w : Fin 8 → OTerm α) (goal : Formula α)
    (h : Known i r c Γ a b v l s t kept d dh dTail removed rawDL rawDR p fullRows rowsL rowsR pL pR pJoin oldJoin w)
    (next : SplitCases (literalData i r) c permutation Γ a b v goal) :
    Pr (literalData i r) c Γ goal := by
  apply exact_OriginalAppendTwoPairs (w 0) pL (w 2) pR goal
  intro β j Δ tl tr q keep al ar aq
  let W : Fin 8 → OTerm β := fun u => (w u).relabel j
  exact exact_OriginalCertifiedPreparedAtAppends i r c (a.relabel j) (b.relabel j) (v.relabel j)
    (l.relabel j) (s.relabel j) (t.relabel j) (kept.relabel j) (d.relabel j) (dh.relabel j)
    (dTail.relabel j) (removed.relabel j) (rawDL.relabel j) (rawDR.relabel j) (p.relabel j)
    (fullRows.relabel j) (rowsL.relabel j) (rowsR.relabel j) (pL.relabel j) (pR.relabel j)
    (pJoin.relabel j) (oldJoin.relabel j) W (goal.relabel j) (relocate i r c h j keep) tl tr q al ar aq
    (exact_OriginalSplitCasesRelabel (literalData i r) c permutation a b v goal next j keep)

#print axioms exact_OriginalCertifiedPreparedCases
end LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedPreparedCasesProof
