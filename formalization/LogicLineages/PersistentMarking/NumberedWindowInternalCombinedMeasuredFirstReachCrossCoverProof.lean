module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCombinedMeasuredFirstReachTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedCrossCoverProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedCommonCoverProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxInputsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredPairedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationCombinedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredAuxExchangeCompareProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCombinedMeasuredFirstReachProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseDirectedSeen (acceptEdge edgeTape)
open NumberedWindowInternalSparseScalarEdgeOpenChecks (exact_OpenPackedScalarEdge)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalMeasuredAuxExchangeTargets (measuredExchange)
open NumberedWindowInternalMeasuredAuxExchangeCompareProof (compareCases)
open NumberedWindowInternalCoverCombinedRestrictedMeasuredPairedProof (measuredParentEdge)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationCombinedProof (pairedParentEdges)
open NumberedWindowInternalCoverCombinedRestrictedCommonCoverProof (exact_OpenCoverCombinedRestrictedCommonCover)
open NumberedWindowInternalCoverCombinedRestrictedWrappedAuxInputsProof (exact_OpenCoverThinMatchingWindowInputs)
open NumberedWindowInternalCoverCombinedRestrictedCrossCoverProof (exact_OpenCoverThinCrossCover)
open NumberedWindowInternalCombinedMeasuredFirstReachTargets

attribute [local irreducible] programGraph

private theorem heldRename {α β : Type} (E : Program 4) (ctx ty a b : OTerm α) (j : α → β) :
    (acceptEdge E ctx ty a b).relabel j =
      acceptEdge E (ctx.relabel j) (ty.relabel j) (a.relabel j) (b.relabel j) := by
  simp only [acceptEdge,programRename,edgeTape,quadInputsRename,sucRelabel,zRelabel]

theorem exact_InstalledMeasuredCrossCover : ExactInstalledMeasuredCrossCover := by
  intro s V TV M M0 B T base body α Γ ctx ty a b goal K edge use
  obtain ⟨held⟩ := edge
  obtain ⟨openEdge⟩ := exact_OpenPackedScalarEdge K.exchange K.window body α Γ ctx ty a b
  have calls := Derivation.implicationElimination (Derivation.conjunctionLeft openEdge) held
  have windows := Derivation.conjunctionRight calls
  have left : Nonempty (Derivation body Γ (windowAt K.window ctx ty a)) :=
    ⟨Derivation.conjunctionLeft windows⟩
  have right : Nonempty (Derivation body Γ (windowAt K.window ctx ty b)) :=
    ⟨Derivation.conjunctionRight windows⟩
  have pair := pairedParentEdges K.cover s (measuredExchange K.measure K.directed) K.window ctx ty a b ⟨held⟩
  have separated := measuredParentEdge K.measure K.directed K.window ctx ty a b pair.1
  apply compareCases K.measure a b goal separated.2
  intro β i Δ measure keep0 ma mb
  have left' := renameInto left i Δ keep0
  have right' := renameInto right i Δ keep0
  rw [windowRename] at left' right'
  have va := exact_OpenCoverThinMatchingWindowInputs K.cover K.source.W K.source.V s body β Δ
    (ctx.relabel i) (ty.relabel i) (a.relabel i) left'
  have vb := exact_OpenCoverThinMatchingWindowInputs K.cover K.source.W K.source.V s body β Δ
    (ctx.relabel i) (ty.relabel i) (b.relabel i) right'
  apply exact_OpenCoverCombinedRestrictedCommonCover V TV M M0 B T s body β Δ
    (a.relabel i) (b.relabel i) measure (goal.relabel i) va.valid vb.valid ma mb
  intro γ j Θ vertices keep1 ca cb
  have left'' := renameInto left' j Θ keep1
  have right'' := renameInto right' j Θ keep1
  rw [windowRename] at left'' right''
  have cover := exact_OpenCoverThinCrossCover K.cover K.source.W K.source.V s body γ Θ
    ((ctx.relabel i).relabel j) ((ty.relabel i).relabel j)
    ((a.relabel i).relabel j) ((b.relabel i).relabel j) vertices left'' right'' ca cb
  have edge' := renameInto ⟨held⟩ i Δ keep0
  have edge'' := renameInto edge' j Θ keep1
  have keep (p : Formula α) (hp : p ∈ Γ) : p.relabel (j ∘ i) ∈ Θ := by
    rw [← formulaRelabelComposition]
    exact keep1 _ (keep0 p hp)
  rw [formulaRelabelComposition]
  refine use γ (j ∘ i) Θ vertices keep ?_ ?_
  · simpa only [Term.relabel_relabel] using cover
  · simpa only [heldRename, Term.relabel_relabel] using edge''

end LogicLineages.PersistentMarking.NumberedWindowInternalCombinedMeasuredFirstReachProof
