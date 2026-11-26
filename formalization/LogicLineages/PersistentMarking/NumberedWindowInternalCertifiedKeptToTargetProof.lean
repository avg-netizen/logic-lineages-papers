module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedPreparedCasesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginInsertionRepackProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptCompleteProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptSplitCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanRoutedHeadProof
import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedKeptToTargetProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalCertifiedUnionStepProof (Pr SplitCases)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalOriginKeptSplitTargets (evidence piece splitExists)
open NumberedWindowInternalOriginKeptSplitCasesProof (exact_OriginalKeptSplitCases)
open NumberedWindowInternalOriginKeptCompleteProof (exact_OriginalKeptSplit)
open NumberedWindowInternalOriginInsertionRepackProof (exact_OriginalInsertionWithRemovedRepack)
open NumberedWindowInternalProjectedCountInductionTargets (project)
open NumberedWindowInternalProjectedCountInductionSyntaxProof (projectRename)
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept)
open NumberedWindowInternalOpenOriginScanRoutedHeadProof (loopRename)
open NumberedWindowInternalLiteralTypedPartitionProof (Typed)
open NumberedWindowInternalRawUnionFromEquivalentPartsProof (App Cmp)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalCertifiedPreparedTargets (Known)
open NumberedWindowInternalCertifiedPreparedCasesProof (exact_OriginalCertifiedPreparedCases)
open NumberedWindowInternalCertifiedOriginCasesRenameProof (exact_OriginalSplitCasesRelabel)

attribute [local irreducible] programGraph

/-- Real original typed/input reports that survive the choice of the
origin-labelled kept/removed witnesses and the two inserted tapes. -/
structure Before (i : Program 1) (r : Program 3) (c : Nat) {α : Type} (Γ : List (Formula α))
    (a b v ls rs t kept d dh dTail removed p fullRows oldJoin : OTerm α) : Prop where
  leftParse : Pr (literalData i r) c Γ (unary parser (suc ls) a)
  rightParse : Pr (literalData i r) c Γ (unary parser (suc rs) b)
  targetParse : Pr (literalData i r) c Γ (unary parser (suc t) v)
  leftTyped : Pr (literalData i r) c Γ (Typed i ls)
  rightTyped : Pr (literalData i r) c Γ (Typed i rs)
  targetTyped : Pr (literalData i r) c Γ (Typed i t)
  removedCons : Pr (literalData i r) c Γ (consGraph d dh dTail)
  removedParse : Pr (literalData i r) c Γ (unary parser (suc d) removed)
  oldScan : Pr (literalData i r) c Γ (loopAccept r fullRows removed)
  oldProject : Pr (literalData i r) c Γ (project p fullRows)
  oldAppend : Pr (literalData i r) c Γ (App kept p oldJoin)
  oldCount : Pr (literalData i r) c Γ (Cmp t oldJoin)

variable {α β : Type} {Γ : List (Formula α)} {Δ : List (Formula β)}

private theorem move (i : Program 1) (r : Program 3) (c : Nat)
    {a b v ls rs t kept d dh dTail removed p fullRows oldJoin : OTerm α}
    (h : Before i r c Γ a b v ls rs t kept d dh dTail removed p fullRows oldJoin)
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    Before i r c Δ (a.relabel j) (b.relabel j) (v.relabel j) (ls.relabel j) (rs.relabel j)
      (t.relabel j) (kept.relabel j) (d.relabel j) (dh.relabel j) (dTail.relabel j)
      (removed.relabel j) (p.relabel j) (fullRows.relabel j) (oldJoin.relabel j) := by
  constructor
  · exact renameParser a ls h.leftParse j Δ keep
  · exact renameParser b rs h.rightParse j Δ keep
  · exact renameParser v t h.targetParse j Δ keep
  · simpa only [Typed,unaryRename,sucRelabel,zRelabel] using renameInto h.leftTyped j Δ keep
  · simpa only [Typed,unaryRename,sucRelabel,zRelabel] using renameInto h.rightTyped j Δ keep
  · simpa only [Typed,unaryRename,sucRelabel,zRelabel] using renameInto h.targetTyped j Δ keep
  · simpa only [consGraphRename] using renameInto h.removedCons j Δ keep
  · exact renameParser removed d h.removedParse j Δ keep
  · simpa only [loopRename] using renameInto h.oldScan j Δ keep
  · simpa only [projectRename] using renameInto h.oldProject j Δ keep
  · exact renamePair append oldJoin kept p h.oldAppend j keep
  · simpa only [Cmp,sucRelabel,zRelabel] using renamePair permutation (suc z) t oldJoin h.oldCount j keep

private theorem opened (i : Program 1) (r : Program 3) (c : Nat)
    (a b v ls rs t kept d dh dTail removed p fullRows oldJoin : OTerm α)
    (w : Fin 8 → OTerm α) (goal : Formula α)
    (h : Before i r c Γ a b v ls rs t kept d dh dTail removed p fullRows oldJoin)
    (pays : Pr (literalData i r) c Γ (evidence ls rs kept d w))
    (next : SplitCases (literalData i r) c permutation Γ a b v goal) :
    Pr (literalData i r) c Γ goal := by
  obtain ⟨e⟩ := pays
  let ex := Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight e))
  apply exact_OriginalInsertionWithRemovedRepack r fullRows removed d (w 1) (w 3) (w 7) p goal
    h.removedParse ⟨Derivation.conjunctionLeft ex⟩ ⟨Derivation.conjunctionRight ex⟩ h.oldScan h.oldProject
  intro β j Δ rawDL rawDR rowsL rowsR pL pR pJoin keep allocated
  let W : Fin 8 → OTerm β := fun u => (w u).relabel j
  have old := move i r c h j keep
  have er : Pr (literalData i r) c Δ (evidence (ls.relabel j) (rs.relabel j) (kept.relabel j) (d.relabel j) W) := by
    simpa only [evidence,piece,conjunctionRename,programRename,binaryInputsRename,sucRelabel,zRelabel,W] using
      renameInto (Nonempty.intro e) j Δ keep
  have data' : Known i r c Δ (a.relabel j) (b.relabel j) (v.relabel j)
      (ls.relabel j) (rs.relabel j) (t.relabel j) (kept.relabel j) (d.relabel j)
      (dh.relabel j) (dTail.relabel j) (removed.relabel j) rawDL rawDR (p.relabel j)
      (fullRows.relabel j) rowsL rowsR pL pR pJoin (oldJoin.relabel j) W :=
    ⟨old.leftParse,old.rightParse,old.targetParse,old.leftTyped,old.rightTyped,old.targetTyped,
      old.removedCons,er,allocated.removedPools,allocated.loopL,allocated.loopR,allocated.projectL,
      allocated.projectR,allocated.orderedProjection,allocated.countProjection,old.oldAppend,old.oldCount⟩
  exact exact_OriginalCertifiedPreparedCases i r c (a.relabel j) (b.relabel j) (v.relabel j)
    (ls.relabel j) (rs.relabel j) (t.relabel j) (kept.relabel j) (d.relabel j)
    (dh.relabel j) (dTail.relabel j) (removed.relabel j) rawDL rawDR (p.relabel j)
    (fullRows.relabel j) rowsL rowsR pL pR pJoin (oldJoin.relabel j) W (goal.relabel j) data'
    (exact_OriginalSplitCasesRelabel (literalData i r) c permutation a b v goal next j keep)

/-- Starting with the actual whole source balance, derive the kept and
removed origin witnesses and all actual insertion/projection/target
certificates, without a supplied origin splitter. -/
theorem exact_OriginalCertifiedKeptToTarget (i : Program 1) (r : Program 3) (c : Nat)
    (a b v ls rs t kept d dh dTail removed p fullRows oldJoin srcJoin certJoin : OTerm α)
    (goal : Formula α)
    (h : Before i r c Γ a b v ls rs t kept d dh dTail removed p fullRows oldJoin)
    (src : Pr (literalData i r) c Γ (App ls rs srcJoin))
    (cert : Pr (literalData i r) c Γ (App kept d certJoin))
    (bal : Pr (literalData i r) c Γ (Cmp srcJoin certJoin))
    (next : SplitCases (literalData i r) c permutation Γ a b v goal) :
    Pr (literalData i r) c Γ goal := by
  have ex := exact_OriginalKeptSplit ls rs kept d srcJoin certJoin src cert bal
  apply exact_OriginalKeptSplitCases ls rs kept d goal ex
  intro β j Δ w keep ev
  exact opened i r c (a.relabel j) (b.relabel j) (v.relabel j)
    (ls.relabel j) (rs.relabel j) (t.relabel j) (kept.relabel j) (d.relabel j)
    (dh.relabel j) (dTail.relabel j) (removed.relabel j) (p.relabel j) (fullRows.relabel j)
    (oldJoin.relabel j) w (goal.relabel j) (move i r c h j keep) ev
    (exact_OriginalSplitCasesRelabel (literalData i r) c permutation a b v goal next j keep)

#print axioms exact_OriginalCertifiedKeptToTarget
end LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedKeptToTargetProof
