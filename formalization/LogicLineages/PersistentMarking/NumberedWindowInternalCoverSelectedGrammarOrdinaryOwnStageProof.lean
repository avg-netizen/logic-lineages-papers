module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOpenStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnStageProof
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
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTermPartProof (ordinaryRename exact_OpenSelectedOrdinaryInTermPart)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem fromRange (d H K M ids prev prevTerms prevArgs next nextTerms nextArgs h a : OTerm α)
    (before : Nonempty (Derivation body Γ (observed d H K M prev prevTerms prevArgs)))
    (after : Nonempty (Derivation body Γ (observed (suc d) H K M next nextTerms nextArgs)))
    (range : Nonempty (Derivation body Γ (rangeReport ids (suc M))))
    (ht : Nonempty (Derivation body Γ (memberGraph H h)))
    (hq : Nonempty (Derivation body Γ (memberGraph prevArgs a))) :
    Nonempty (Derivation body Γ (memberGraph nextTerms (ordinaryKey h a))) := by
  obtain ⟨before⟩ := before
  obtain ⟨after⟩ := after
  have t := Derivation.conjunctionRight before
  have u := Derivation.conjunctionRight after
  obtain ⟨split⟩ := exact_OpenSelectedGrammarSuccessorSplit body α Γ prev next d H K M ids
    prevTerms prevArgs nextTerms nextArgs
    ⟨Derivation.conjunctionLeft before⟩ ⟨Derivation.conjunctionLeft after⟩
    ⟨Derivation.conjunctionLeft t⟩ ⟨Derivation.conjunctionRight t⟩ range
    ⟨Derivation.conjunctionLeft u⟩ ⟨Derivation.conjunctionRight u⟩
  exact exact_OpenSelectedOrdinaryInTermPart body α Γ nextTerms H K ids prevTerms prevArgs h a
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight split)⟩ ht hq

theorem exact_OpenSelectedGrammarOrdinaryFromPredecessor : ExactOpenSelectedGrammarOrdinaryFromPredecessor := by
  intro body α Γ d H K M prev prevTerms prevArgs next nextTerms nextArgs h a before after ht hq
  apply programCases ascendingRange ![suc M] _
  intro β j Δ ids keep range
  rw [graphRename,ordinaryRename]
  simp only [unaryTapeRename,sucRelabel] at range
  have before' := renameInto before j Δ keep
  have after' := renameInto after j Δ keep
  have ht' := renameInto ht j Δ keep
  rw [observedRename] at before' after'
  simp only [sucRelabel] at after'
  have hq' := renameInto hq j Δ keep
  rw [graphRename] at ht' hq'
  exact fromRange (d.relabel j) (H.relabel j) (K.relabel j) (M.relabel j) ids
    (prev.relabel j) (prevTerms.relabel j) (prevArgs.relabel j)
    (next.relabel j) (nextTerms.relabel j) (nextArgs.relabel j) (h.relabel j) (a.relabel j)
    before' after' range ht' hq'

#print axioms exact_OpenSelectedGrammarOrdinaryFromPredecessor

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnStageProof
