module
public import LogicLineages.PersistentMarking.NumberedWindowInternalChangedSideFromScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanRoutedHeadProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginEmptyRemovedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginUnchangedAlignProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalScratchSideSeedProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename outputTransport)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (congSuc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalConsUnionReportBuildProof (Report)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (scratchTargets)
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept)
open NumberedWindowInternalOpenOriginScanRoutedHeadProof (loopRename)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser)
open NumberedWindowInternalDirectBoundaryGuardsTargets (typedScratch)
open NumberedWindowInternalOriginEmptyRemovedProof (exact_OpenEmptyRemovedProjectionZero)
open NumberedWindowInternalOriginUnchangedAlignProof (exact_OpenOriginUnchangedAlign)
open NumberedWindowInternalChangedSideFromScratchProof (Body ScratchSide)

attribute [local irreducible] programGraph

/-- The same actual fixed source, planned target and ordered change
reports, before determining whether this side has an actual removed cons.
The target code is already the actual append output, not a fresh choice. -/
structure ScratchSideSeed (i : Program 1) (r : Program 3) (c : Nat)
    {α : Type} (Γ : List (Formula α))
    (s removed ds dt dk dd da projected srcJoin : OTerm α) : Prop where
  sourceParse : Report (B := Body i r c) (Γ := Γ) parser (suc ds) ![s]
  removedParse : Report (B := Body i r c) (Γ := Γ) parser (suc dd) ![removed]
  sourceTyped : Report (B := Body i r c) (Γ := Γ) (typedScratch i) (suc z) ![ds]
  targetTyped : Report (B := Body i r c) (Γ := Γ) (typedScratch i) (suc z) ![dt]
  sourceAppend : Report (B := Body i r c) (Γ := Γ) append srcJoin ![dk,dd]
  sourceCount : Report (B := Body i r c) (Γ := Γ) permutation (suc z) ![ds,srcJoin]
  targetAppend : Report (B := Body i r c) (Γ := Γ) append dt ![dk,projected]
  projection : Report (B := Body i r c) (Γ := Γ) scratchTargets (suc projected) ![da]
  rows : Nonempty (Derivation (Body i r c) Γ (loopAccept r da removed))

variable {α β : Type} {Γ : List (Formula α)} {Δ : List (Formula β)}

theorem relocateScratchSideSeed (i : Program 1) (r : Program 3) (c : Nat)
    {s d ds dt dk dd da projected sj : OTerm α}
    (p : ScratchSideSeed i r c Γ s d ds dt dk dd da projected sj)
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    ScratchSideSeed i r c Δ (s.relabel j) (d.relabel j) (ds.relabel j) (dt.relabel j)
      (dk.relabel j) (dd.relabel j) (da.relabel j) (projected.relabel j) (sj.relabel j) := by
  constructor
  · exact renameParser s ds p.sourceParse j Δ keep
  · exact renameParser d dd p.removedParse j Δ keep
  · simpa only [programRename,inputsRename,sucRelabel,zRelabel] using renameInto p.sourceTyped j Δ keep
  · simpa only [programRename,inputsRename,sucRelabel,zRelabel] using renameInto p.targetTyped j Δ keep
  · exact renamePair append sj dk dd p.sourceAppend j keep
  · simpa only [sucRelabel,zRelabel] using renamePair permutation (suc z) ds sj p.sourceCount j keep
  · exact renamePair append dt dk projected p.targetAppend j keep
  · simpa only [programRename,inputsRename,sucRelabel] using renameInto p.projection j Δ keep
  · simpa only [loopRename] using renameInto p.rows j Δ keep

theorem exact_OriginalScratchSideOfCons {i : Program 1} {r : Program 3} {c : Nat}
    {s d ds dt dk dd da projected sj h t : OTerm α}
    (p : ScratchSideSeed i r c Γ s d ds dt dk dd da projected sj)
    (cell : Nonempty (Derivation (Body i r c) Γ (consGraph dd h t))) :
    ScratchSide i r c Γ s d ds dt dk dd da projected sj h t :=
  ⟨p.sourceParse,p.removedParse,p.sourceTyped,p.targetTyped,cell,p.sourceAppend,p.sourceCount,
    p.targetAppend,p.projection,p.rows⟩

theorem relocateScratchSide (i : Program 1) (r : Program 3) (c : Nat)
    {s d ds dt dk dd da projected sj h t : OTerm α}
    (p : ScratchSide i r c Γ s d ds dt dk dd da projected sj h t)
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    ScratchSide i r c Δ (s.relabel j) (d.relabel j) (ds.relabel j) (dt.relabel j)
      (dk.relabel j) (dd.relabel j) (da.relabel j) (projected.relabel j) (sj.relabel j)
      (h.relabel j) (t.relabel j) := by
  have seed : ScratchSideSeed i r c Γ s d ds dt dk dd da projected sj :=
    ⟨p.sourceParse,p.removedParse,p.sourceTyped,p.targetTyped,p.sourceAppend,p.sourceCount,
      p.targetAppend,p.projection,p.rows⟩
  have cell := renameInto p.removedCons j Δ keep
  rw [consGraphRename] at cell
  exact exact_OriginalScratchSideOfCons (relocateScratchSideSeed i r c seed j keep) cell

/-- An actually empty removed code implies an empty actual insertion
projection under the existing scan. The exact count is transferred to
the already held target join, in source-to-planned orientation. -/
theorem exact_OriginalUnchangedSideCount {i : Program 1} {r : Program 3} {c : Nat}
    {s d ds dt dk dd da projected sj : OTerm α}
    (p : ScratchSideSeed i r c Γ s d ds dt dk dd da projected sj)
    (empty : Nonempty (Derivation (Body i r c) Γ (eqn dd z))) :
    Report (B := Body i r c) (Γ := Γ) permutation (suc z) ![ds,dt] := by
  obtain ⟨emptyEq⟩ := empty
  have parsedNil : Nonempty (Derivation (Body i r c) Γ (unary parser (suc z) d)) :=
    outputTransport parser (suc dd) (suc z) ![d] ⟨congSuc emptyEq⟩ p.removedParse
  have projectionNil := exact_OpenEmptyRemovedProjectionZero r (Body i r c) α Γ da d projected
    parsedNil p.rows p.projection
  exact exact_OpenOriginUnchangedAlign (Body i r c) α Γ ds dk dd projected sj dt
    ⟨emptyEq⟩ projectionNil p.sourceAppend p.targetAppend p.sourceCount

#print axioms relocateScratchSideSeed
#print axioms exact_OriginalScratchSideOfCons
#print axioms relocateScratchSide
#print axioms exact_OriginalUnchangedSideCount
end LogicLineages.PersistentMarking.NumberedWindowInternalScratchSideSeedProof
