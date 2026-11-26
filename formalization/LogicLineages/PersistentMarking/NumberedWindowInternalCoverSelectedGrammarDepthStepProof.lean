module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthBaseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthBaseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOpenRowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorInclusionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsOpenDataProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthStepProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalCoverAscendingRangeTargets (rangeReport ascendingRange)
open NumberedWindowInternalCoverSelectedSuccessorInclusionProof (exact_OpenSelectedCoverSuccessorInclusion)
open NumberedWindowInternalCoverArgumentCellsOpenDataProof (unaryTapeRename)
open NumberedWindowInternalCoverSelectedGrammarOpenRowProof (exact_OpenSelectedGrammarSuccessorRow)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed pairInclusion)
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedRename)
open NumberedWindowInternalCoverSelectedGrammarWidthObservationProof (observationCases)
open NumberedWindowInternalCoverSelectedGrammarWidthBaseProof (includeFromEquality)
open NumberedWindowInternalCoverSelectedGrammarDepthTargets
open NumberedWindowInternalCoverSelectedGrammarDepthSyntaxProof (adjacentRename)
open NumberedWindowInternalCoverSelectedGrammarDepthBindingProof (buildDepth consumeDepth)
open NumberedWindowInternalCoverSelectedGrammarDepthBaseProof (inclusionRename)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Use one actual range for both original rows; the middle observation
is both the lower actual successor and the upper actual predecessor. -/
theorem advanceAdjacent (d H K M ids lo loTerms loArgs old oldTerms oldArgs next nextTerms nextArgs : OTerm α)
    (ih : Nonempty (Derivation body Γ (adjacentAt d H K M)))
    (earlier : Nonempty (Derivation body Γ (observed d H K M lo loTerms loArgs)))
    (smaller : Nonempty (Derivation body Γ (observed (suc d) H K M old oldTerms oldArgs)))
    (larger : Nonempty (Derivation body Γ (observed (suc (suc d)) H K M next nextTerms nextArgs)))
    (range : Nonempty (Derivation body Γ (rangeReport ids (suc M)))) :
    Nonempty (Derivation body Γ (pairInclusion oldTerms nextTerms oldArgs nextArgs)) := by
  obtain ⟨prior⟩ := consumeDepth d (suc d) H K M lo loTerms loArgs old oldTerms oldArgs ih earlier smaller
  have fixedIds := includeFromEquality (body := body) (Γ := Γ) ids ids ⟨refl ids⟩
  obtain ⟨earlier⟩ := earlier
  obtain ⟨smaller⟩ := smaller
  obtain ⟨larger⟩ := larger
  have priorRead := Derivation.conjunctionRight earlier
  have midRead := Derivation.conjunctionRight smaller
  have nextRead := Derivation.conjunctionRight larger
  have low := exact_OpenSelectedGrammarSuccessorRow body α Γ lo old d H K M ids loTerms loArgs
    ⟨Derivation.conjunctionLeft earlier⟩ ⟨Derivation.conjunctionLeft smaller⟩
    ⟨Derivation.conjunctionLeft priorRead⟩ ⟨Derivation.conjunctionRight priorRead⟩ range
  have high := exact_OpenSelectedGrammarSuccessorRow body α Γ old next (suc d) H K M ids oldTerms oldArgs
    ⟨Derivation.conjunctionLeft smaller⟩ ⟨Derivation.conjunctionLeft larger⟩
    ⟨Derivation.conjunctionLeft midRead⟩ ⟨Derivation.conjunctionRight midRead⟩ range
  exact exact_OpenSelectedCoverSuccessorInclusion body α Γ old next oldTerms nextTerms oldArgs nextArgs
    H K ids ids loTerms oldTerms loArgs oldArgs low high
    ⟨Derivation.conjunctionLeft midRead⟩ ⟨Derivation.conjunctionLeft nextRead⟩
    ⟨Derivation.conjunctionRight midRead⟩ ⟨Derivation.conjunctionRight nextRead⟩
    fixedIds ⟨Derivation.conjunctionLeft prior⟩ ⟨Derivation.conjunctionRight prior⟩

private theorem withRange (d H K M lo loTerms loArgs old oldTerms oldArgs next nextTerms nextArgs : OTerm α)
    (ih : Nonempty (Derivation body Γ (adjacentAt d H K M)))
    (earlier : Nonempty (Derivation body Γ (observed d H K M lo loTerms loArgs)))
    (smaller : Nonempty (Derivation body Γ (observed (suc d) H K M old oldTerms oldArgs)))
    (larger : Nonempty (Derivation body Γ (observed (suc (suc d)) H K M next nextTerms nextArgs))) :
    Nonempty (Derivation body Γ (pairInclusion oldTerms nextTerms oldArgs nextArgs)) := by
  apply programCases ascendingRange ![suc M] _
  intro β j Δ ids keep actual
  rw [inclusionRename]
  simp only [unaryTapeRename,sucRelabel] at actual
  have ih' := renameInto ih j Δ keep
  have p := renameInto earlier j Δ keep
  have s := renameInto smaller j Δ keep
  have l := renameInto larger j Δ keep
  rw [adjacentRename] at ih'
  rw [observedRename] at p s l
  simp only [sucRelabel] at s l
  exact advanceAdjacent (d.relabel j) (H.relabel j) (K.relabel j) (M.relabel j) ids
    (lo.relabel j) (loTerms.relabel j) (loArgs.relabel j)
    (old.relabel j) (oldTerms.relabel j) (oldArgs.relabel j)
    (next.relabel j) (nextTerms.relabel j) (nextArgs.relabel j) ih' p s l actual

private theorem withPrior (d H K M old oldTerms oldArgs next nextTerms nextArgs : OTerm α)
    (ih : Nonempty (Derivation body Γ (adjacentAt d H K M)))
    (middle : Nonempty (Derivation body Γ (observed (suc d) H K M old oldTerms oldArgs)))
    (larger : Nonempty (Derivation body Γ (observed (suc (suc d)) H K M next nextTerms nextArgs))) :
    Nonempty (Derivation body Γ (pairInclusion oldTerms nextTerms oldArgs nextArgs)) := by
  apply observationCases d H K M _
  intro β j Δ earlier earlierTerms earlierArgs keep actual
  rw [inclusionRename]
  have ih' := renameInto ih j Δ keep
  have s := renameInto middle j Δ keep
  have l := renameInto larger j Δ keep
  rw [adjacentRename] at ih'
  rw [observedRename] at s l
  simp only [sucRelabel] at s l
  exact withRange (d.relabel j) (H.relabel j) (K.relabel j) (M.relabel j)
    earlier earlierTerms earlierArgs (old.relabel j) (oldTerms.relabel j) (oldArgs.relabel j)
    (next.relabel j) (nextTerms.relabel j) (nextArgs.relabel j) ih' actual s l

theorem adjacentAtSuccessor (d H K M : OTerm α)
    (ih : Nonempty (Derivation body Γ (adjacentAt d H K M))) :
    Nonempty (Derivation body Γ (adjacentAt (suc d) H K M)) := by
  apply buildDepth (suc d) (suc (suc d)) H K M
  intro β j Δ old oldTerms oldArgs next nextTerms nextArgs keep s l
  have ih' := renameInto ih j Δ keep
  rw [adjacentRename] at ih'
  simp only [sucRelabel] at s l
  exact withPrior (d.relabel j) (H.relabel j) (K.relabel j) (M.relabel j)
    old oldTerms oldArgs next nextTerms nextArgs ih' s l

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthStepProof
