module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumberedOwnTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumberedOwnTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOpenProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOpenStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumberedOwnStageProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc sucRelabel)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalCoverAscendingRangeTargets (ascendingRange rangeReport)
open NumberedWindowInternalCoverArgumentCellsOpenDataProof (unaryTapeRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedRename)
open NumberedWindowInternalCoverSelectedGrammarOpenStepProof (exact_OpenSelectedGrammarSuccessorSplit)
open NumberedWindowInternalCoverSelectedGrammarNumberedOwnTargets
open NumberedWindowInternalCoverSelectedGrammarNumberedOwnTermPartProof (exact_OpenSelectedNumberedInTermPart)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalCoverNumberedLayerOpenDataProof (numberedRename)
open NumberedWindowInternalCoverAscendingRangeOpenProof (exact_OpenCoverAscendingRangeMember)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem fromRange (d H K M ids prev prevTerms prevArgs next nextTerms nextArgs h ty k l r : OTerm α)
    (before : Nonempty (Derivation body Γ (observed d H K M prev prevTerms prevArgs)))
    (after : Nonempty (Derivation body Γ (observed (suc d) H K M next nextTerms nextArgs)))
    (range : Nonempty (Derivation body Γ (rangeReport ids (suc M))))
    (ht : Nonempty (Derivation body Γ (memberGraph H h)))
    (hy : Nonempty (Derivation body Γ (memberGraph K ty)))
    (hk : Nonempty (Derivation body Γ (ltF k (suc M))))
    (hl : Nonempty (Derivation body Γ (memberGraph prevArgs l)))
    (hr : Nonempty (Derivation body Γ (memberGraph prevArgs r))) :
    Nonempty (Derivation body Γ (memberGraph nextTerms (numberedTerm h ty k l r))) := by
  obtain ⟨before⟩ := before
  obtain ⟨after⟩ := after
  have t := Derivation.conjunctionRight before
  have u := Derivation.conjunctionRight after
  obtain ⟨split⟩ := exact_OpenSelectedGrammarSuccessorSplit body α Γ prev next d H K M ids
    prevTerms prevArgs nextTerms nextArgs
    ⟨Derivation.conjunctionLeft before⟩ ⟨Derivation.conjunctionLeft after⟩
    ⟨Derivation.conjunctionLeft t⟩ ⟨Derivation.conjunctionRight t⟩ range
    ⟨Derivation.conjunctionLeft u⟩ ⟨Derivation.conjunctionRight u⟩
  have id := exact_OpenCoverAscendingRangeMember body α Γ ids (suc M) k range hk
  exact exact_OpenSelectedNumberedInTermPart body α Γ nextTerms H K ids prevTerms prevArgs h ty k l r
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight split)⟩ ht hy id hl hr

theorem exact_OpenSelectedGrammarNumberedFromPredecessor : ExactOpenSelectedGrammarNumberedFromPredecessor := by
  intro body α Γ d H K M prev prevTerms prevArgs next nextTerms nextArgs h ty k l r before after ht hy hk hl hr
  apply programCases ascendingRange ![suc M] _
  intro β j Δ ids keep range
  rw [graphRename,numberedRename]
  simp only [unaryTapeRename,sucRelabel] at range
  have before' := renameInto before j Δ keep
  have after' := renameInto after j Δ keep
  have ht' := renameInto ht j Δ keep
  rw [observedRename] at before' after'
  simp only [sucRelabel] at after'
  have hy' := renameInto hy j Δ keep
  have hk' := renameInto hk j Δ keep
  have hl' := renameInto hl j Δ keep
  have hr' := renameInto hr j Δ keep
  rw [graphRename] at ht' hy' hl' hr'
  simp only [orderRename,sucRelabel] at hk'
  exact fromRange (d.relabel j) (H.relabel j) (K.relabel j) (M.relabel j) ids
    (prev.relabel j) (prevTerms.relabel j) (prevArgs.relabel j)
    (next.relabel j) (nextTerms.relabel j) (nextArgs.relabel j)
    (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j)
    before' after' range ht' hy' hk' hl' hr'

#print axioms exact_OpenSelectedGrammarNumberedFromPredecessor

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumberedOwnStageProof
