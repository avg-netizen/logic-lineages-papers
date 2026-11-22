module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNullaryTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNullaryTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNullaryEmptyArgsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOpenStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNullaryStageProof
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
open NumberedWindowInternalCoverSelectedGrammarWidthObservationProof (observationCases)
open NumberedWindowInternalCoverSelectedGrammarOpenStepProof (exact_OpenSelectedGrammarSuccessorSplit)
open NumberedWindowInternalCoverSelectedGrammarNullaryTargets
open NumberedWindowInternalCoverSelectedGrammarNullaryTermPartProof
  (nullaryRename exact_OpenSelectedNullaryInTermPart)
open NumberedWindowInternalCoverSelectedGrammarNullaryEmptyArgsProof (exact_OpenSelectedGrammarEmptyArgs)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem fromRange (d H K M ids prev prevTerms prevArgs next nextTerms nextArgs h : OTerm α)
    (before : Nonempty (Derivation body Γ (observed d H K M prev prevTerms prevArgs)))
    (after : Nonempty (Derivation body Γ (observed (suc d) H K M next nextTerms nextArgs)))
    (range : Nonempty (Derivation body Γ (rangeReport ids (suc M))))
    (ht : Nonempty (Derivation body Γ (memberGraph H h))) :
    Nonempty (Derivation body Γ (memberGraph nextTerms (nullaryKey h))) := by
  have empty := exact_OpenSelectedGrammarEmptyArgs body α Γ d H K M prev prevTerms prevArgs before
  obtain ⟨before⟩ := before
  obtain ⟨after⟩ := after
  have t := Derivation.conjunctionRight before
  have u := Derivation.conjunctionRight after
  obtain ⟨split⟩ := exact_OpenSelectedGrammarSuccessorSplit body α Γ prev next d H K M ids
    prevTerms prevArgs nextTerms nextArgs
    ⟨Derivation.conjunctionLeft before⟩ ⟨Derivation.conjunctionLeft after⟩
    ⟨Derivation.conjunctionLeft t⟩ ⟨Derivation.conjunctionRight t⟩ range
    ⟨Derivation.conjunctionLeft u⟩ ⟨Derivation.conjunctionRight u⟩
  exact exact_OpenSelectedNullaryInTermPart body α Γ nextTerms H K ids prevTerms prevArgs h
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight split)⟩ ht empty

private theorem fromBefore (d H K M prev prevTerms prevArgs next nextTerms nextArgs h : OTerm α)
    (before : Nonempty (Derivation body Γ (observed d H K M prev prevTerms prevArgs)))
    (after : Nonempty (Derivation body Γ (observed (suc d) H K M next nextTerms nextArgs)))
    (ht : Nonempty (Derivation body Γ (memberGraph H h))) :
    Nonempty (Derivation body Γ (memberGraph nextTerms (nullaryKey h))) := by
  apply programCases ascendingRange ![suc M] _
  intro β j Δ ids keep range
  rw [graphRename,nullaryRename]
  simp only [unaryTapeRename,sucRelabel] at range
  have before' := renameInto before j Δ keep
  have after' := renameInto after j Δ keep
  have ht' := renameInto ht j Δ keep
  rw [observedRename] at before' after'
  simp only [sucRelabel] at after'
  rw [graphRename] at ht'
  exact fromRange (d.relabel j) (H.relabel j) (K.relabel j) (M.relabel j) ids
    (prev.relabel j) (prevTerms.relabel j) (prevArgs.relabel j)
    (next.relabel j) (nextTerms.relabel j) (nextArgs.relabel j) (h.relabel j)
    before' after' range ht'

theorem exact_OpenSelectedGrammarNullaryAtSuccessor : ExactOpenSelectedGrammarNullaryAtSuccessor := by
  intro body α Γ d H K M next out args h after ht
  apply observationCases d H K M _
  intro β j Δ prev prevTerms prevArgs keep before
  rw [graphRename,nullaryRename]
  have after' := renameInto after j Δ keep
  have ht' := renameInto ht j Δ keep
  simp only [observedRename,sucRelabel] at after'
  rw [graphRename] at ht'
  exact fromBefore (d.relabel j) (H.relabel j) (K.relabel j) (M.relabel j)
    prev prevTerms prevArgs (next.relabel j) (out.relabel j) (args.relabel j) (h.relabel j)
    before after' ht'

#print axioms exact_OpenSelectedGrammarNullaryAtSuccessor

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNullaryStageProof
