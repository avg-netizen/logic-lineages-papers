module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNonemptyArgsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNonemptyArgsRowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOpenStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNonemptyArgsStageProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc sucRelabel)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalCoverAscendingRangeTargets (ascendingRange rangeReport)
open NumberedWindowInternalCoverArgumentCellsOpenDataProof (unaryTapeRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedRename)
open NumberedWindowInternalCoverSelectedGrammarOpenStepProof (exact_OpenSelectedGrammarSuccessorSplit)
open NumberedWindowInternalCoverSelectedGrammarNonemptyArgsTargets
open NumberedWindowInternalCoverSelectedGrammarNonemptyArgsRowProof (exact_OpenSelectedNonemptyArgsRow)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem fromRange (d H K M ids prev prevTerms prevArgs next nextTerms nextArgs q tail : OTerm α)
    (before : Nonempty (Derivation body Γ (observed d H K M prev prevTerms prevArgs)))
    (after : Nonempty (Derivation body Γ (observed (suc d) H K M next nextTerms nextArgs)))
    (range : Nonempty (Derivation body Γ (rangeReport ids (suc M))))
    (hq : Nonempty (Derivation body Γ (memberGraph prevTerms q)))
    (ha : Nonempty (Derivation body Γ (memberGraph prevArgs tail))) :
    Nonempty (Derivation body Γ (memberGraph nextArgs (rawCons q tail))) := by
  obtain ⟨before⟩ := before
  obtain ⟨after⟩ := after
  have t := Derivation.conjunctionRight before
  have u := Derivation.conjunctionRight after
  obtain ⟨split⟩ := exact_OpenSelectedGrammarSuccessorSplit body α Γ prev next d H K M ids
    prevTerms prevArgs nextTerms nextArgs
    ⟨Derivation.conjunctionLeft before⟩ ⟨Derivation.conjunctionLeft after⟩
    ⟨Derivation.conjunctionLeft t⟩ ⟨Derivation.conjunctionRight t⟩ range
    ⟨Derivation.conjunctionLeft u⟩ ⟨Derivation.conjunctionRight u⟩
  exact exact_OpenSelectedNonemptyArgsRow body α Γ nextArgs H K ids prevTerms prevArgs q tail
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight split)⟩ hq ha

theorem exact_OpenSelectedNonemptyArgsFromPredecessor : ExactOpenSelectedNonemptyArgsFromPredecessor := by
  intro body α Γ d H K M prev prevTerms prevArgs next nextTerms nextArgs q tail before after hq ha
  apply programCases ascendingRange ![suc M] _
  intro β j Δ ids keep range
  rw [graphRename,rawConsRename]
  simp only [unaryTapeRename,sucRelabel] at range
  have before' := renameInto before j Δ keep
  have after' := renameInto after j Δ keep
  rw [observedRename] at before' after'
  simp only [sucRelabel] at after'
  have hq' := renameInto hq j Δ keep
  have ha' := renameInto ha j Δ keep
  rw [graphRename] at hq' ha'
  exact fromRange (d.relabel j) (H.relabel j) (K.relabel j) (M.relabel j) ids
    (prev.relabel j) (prevTerms.relabel j) (prevArgs.relabel j)
    (next.relabel j) (nextTerms.relabel j) (nextArgs.relabel j) (q.relabel j) (tail.relabel j)
    before' after' range hq' ha'

#print axioms exact_OpenSelectedNonemptyArgsFromPredecessor

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNonemptyArgsStageProof
