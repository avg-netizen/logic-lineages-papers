module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOriginChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseBoundsArithmeticProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeInclusionTransparentProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalUnpairReverseBoundsArithmeticProof (weakTrans)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverArgumentCellsTargets (axisInclusion)
open NumberedWindowInternalCoverAscendingRangeTargets (rangeReport)
open NumberedWindowInternalCoverAscendingRangeOpenProof (exact_OpenCoverAscendingRangeMember)
open NumberedWindowInternalCoverAscendingRangeOriginChecks (exact_OpenCoverAscendingRangeOrigin)

private theorem unaryTapeRename {α β : Type} (a : OTerm α) (j : α → β) :
    (fun q : Fin 1 => ((![a] : Fin 1 → OTerm α) q).relabel j) = ![a.relabel j] := by
  funext q
  obtain rfl := Fin.eq_zero q
  rfl

private theorem rangeRename {α β : Type} (ids m : OTerm α) (j : α → β) :
    (rangeReport ids (suc m)).relabel j = rangeReport (ids.relabel j) (suc (m.relabel j)) := by
  simp only [rangeReport,programRename,unaryTapeRename,sucRelabel]

/-- Genuine original ascending range reports at both exclusive successor
bounds, with the actual object weak order of maxima, give inclusion of the
two actual physical numeral lists. -/
theorem includeActualRanges :
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (a b m M : OTerm α),
    Nonempty (Derivation body Γ (rangeReport a (suc m))) →
    Nonempty (Derivation body Γ (rangeReport b (suc M))) →
    Nonempty (Derivation body Γ (ltF m (suc M))) →
    Nonempty (Derivation body Γ (axisInclusion a b)) := by
  intro body α Γ a b m M old next weak
  let j : α → α ⊕ Fin 1 := Sum.inl
  let i : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let P := memberGraph (a.relabel j) i
  let Δ := P :: Γ.map (fun q => q.relabel j)
  have keep : ∀ q ∈ Γ, q.relabel j ∈ Δ := by
    intro q h
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,h,rfl⟩)
  have old' := renameInto old j Δ keep
  have next' := renameInto next j Δ keep
  have weak' := renameInto weak j Δ keep
  rw [rangeRename] at old' next'
  rw [orderRename,sucRelabel] at weak'
  have below := exact_OpenCoverAscendingRangeOrigin body _ Δ (a.relabel j)
    (suc (m.relabel j)) i old' ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hit⟩ := exact_OpenCoverAscendingRangeMember body _ Δ (b.relabel j)
    (suc (M.relabel j)) i next' (weakTrans i (m.relabel j) (M.relabel j) below weak')
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction hit)⟩

#print axioms includeActualRanges

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeInclusionTransparentProof
