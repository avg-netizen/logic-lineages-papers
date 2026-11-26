module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxParentTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOpenStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxPredecessorProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc sucRelabel)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalCoverAscendingRangeTargets (ascendingRange rangeReport)
open NumberedWindowInternalCoverArgumentCellsOpenDataProof (unaryTapeRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedRename)
open NumberedWindowInternalCoverSelectedGrammarOpenStepProof (exact_OpenSelectedGrammarSuccessorSplit)
open NumberedWindowInternalCoverSelectedGrammarAuxParentTargets
open NumberedWindowInternalCoverSelectedGrammarAuxTermPartProof (exact_OpenSelectedAuxInTermPart)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem fromRange (d H K M ids prev prevTerms prevArgs next nextTerms nextArgs dom cod fn arg : OTerm α)
    (before : Nonempty (Derivation body Γ (observed d H K M prev prevTerms prevArgs)))
    (after : Nonempty (Derivation body Γ (observed (suc d) H K M next nextTerms nextArgs)))
    (range : Nonempty (Derivation body Γ (rangeReport ids (suc M))))
    (hd : Nonempty (Derivation body Γ (memberGraph K dom)))
    (hc : Nonempty (Derivation body Γ (memberGraph K cod)))
    (hf : Nonempty (Derivation body Γ (memberGraph prevTerms fn)))
    (ha : Nonempty (Derivation body Γ (memberGraph prevTerms arg))) :
    Nonempty (Derivation body Γ (memberGraph nextTerms (auxiliaryTerm dom cod fn arg))) := by
  obtain ⟨before⟩ := before
  obtain ⟨after⟩ := after
  have t := Derivation.conjunctionRight before
  have u := Derivation.conjunctionRight after
  obtain ⟨split⟩ := exact_OpenSelectedGrammarSuccessorSplit body α Γ prev next d H K M ids
    prevTerms prevArgs nextTerms nextArgs
    ⟨Derivation.conjunctionLeft before⟩ ⟨Derivation.conjunctionLeft after⟩
    ⟨Derivation.conjunctionLeft t⟩ ⟨Derivation.conjunctionRight t⟩ range
    ⟨Derivation.conjunctionLeft u⟩ ⟨Derivation.conjunctionRight u⟩
  exact exact_OpenSelectedAuxInTermPart body α Γ nextTerms H K ids prevTerms prevArgs dom cod fn arg
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight split)⟩ hd hc hf ha

theorem exact_OpenSelectedGrammarAuxAtPredecessor : ExactOpenSelectedGrammarAuxAtPredecessor := by
  intro body α Γ d H K M prev prevTerms prevArgs next nextTerms nextArgs dom cod fn arg
    before after hd hc hf ha
  apply programCases ascendingRange ![suc M] _
  intro β j Δ ids keep range
  rw [graphRename,auxiliaryRename]
  simp only [unaryTapeRename,sucRelabel] at range
  have before' := renameInto before j Δ keep
  have after' := renameInto after j Δ keep
  rw [observedRename] at before' after'
  simp only [sucRelabel] at after'
  have hd' := renameInto hd j Δ keep
  have hc' := renameInto hc j Δ keep
  have hf' := renameInto hf j Δ keep
  have ha' := renameInto ha j Δ keep
  rw [graphRename] at hd' hc' hf' ha'
  exact fromRange (d.relabel j) (H.relabel j) (K.relabel j) (M.relabel j) ids
    (prev.relabel j) (prevTerms.relabel j) (prevArgs.relabel j)
    (next.relabel j) (nextTerms.relabel j) (nextArgs.relabel j)
    (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
    before' after' range hd' hc' hf' ha'

#print axioms exact_OpenSelectedGrammarAuxAtPredecessor

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxPredecessorProof
