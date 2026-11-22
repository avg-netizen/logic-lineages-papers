module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOpenRowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorInclusionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeInclusionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTransportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthStepProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc sucRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open NumberedWindowInternalCoverAscendingRangeTargets (rangeReport ascendingRange)
open NumberedWindowInternalCoverAscendingRangeInclusionProof (exact_OpenCoverAscendingRangeInclusion)
open NumberedWindowInternalCoverSelectedSuccessorInclusionProof (exact_OpenSelectedCoverSuccessorInclusion)
open NumberedWindowInternalCoverArgumentCellsOpenDataProof (unaryTapeRename)
open NumberedWindowInternalCoverArgumentCellsTransportProof (axisRename)
open NumberedWindowInternalCoverSelectedGrammarOpenRowProof (exact_OpenSelectedGrammarSuccessorRow)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedRename widthRename)
open NumberedWindowInternalCoverSelectedGrammarWidthObservationProof (observationCases)
open NumberedWindowInternalCoverSelectedGrammarWidthBindingProof (buildWidth consumeWidth)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)}

private theorem pairRename (t t' a a' : OTerm α) (j : α → β) :
    (pairInclusion t t' a a').relabel j =
      pairInclusion (t.relabel j) (t'.relabel j) (a.relabel j) (a'.relabel j) := by
  unfold pairInclusion
  rw [conjunctionRename,axisRename,axisRename]

private theorem rangeRename (ids M : OTerm α) (j : α → β) :
    (rangeReport ids (suc M)).relabel j = rangeReport (ids.relabel j) (suc (M.relabel j)) := by
  simp only [rangeReport,programRename,unaryTapeRename,sucRelabel]

/-- Physical one-step inclusion at the same predecessor depth.
Widths differ only through the two actual original range reports. -/
theorem advanceWidth (d H K m M ids ids'
    old oldTerms oldArgs next nextTerms nextArgs lo loTerms loArgs hi hiTerms hiArgs : OTerm α)
    (bound : Nonempty (Derivation body Γ (ltF m (suc M))))
    (ih : Nonempty (Derivation body Γ (widthAt d H K m M)))
    (loRange : Nonempty (Derivation body Γ (rangeReport ids (suc m))))
    (hiRange : Nonempty (Derivation body Γ (rangeReport ids' (suc M))))
    (priorLo : Nonempty (Derivation body Γ (observed d H K m lo loTerms loArgs)))
    (priorHi : Nonempty (Derivation body Γ (observed d H K M hi hiTerms hiArgs)))
    (small : Nonempty (Derivation body Γ (observed (suc d) H K m old oldTerms oldArgs)))
    (large : Nonempty (Derivation body Γ (observed (suc d) H K M next nextTerms nextArgs))) :
    Nonempty (Derivation body Γ (pairInclusion oldTerms nextTerms oldArgs nextArgs)) := by
  obtain ⟨prior⟩ := consumeWidth d H K m M lo loTerms loArgs hi hiTerms hiArgs ih priorLo priorHi
  have includeIds := exact_OpenCoverAscendingRangeInclusion body α Γ ids ids' m M loRange hiRange bound
  obtain ⟨priorLo⟩ := priorLo
  obtain ⟨priorHi⟩ := priorHi
  obtain ⟨small⟩ := small
  obtain ⟨large⟩ := large
  have prevLo := Derivation.conjunctionRight priorLo
  have prevHi := Derivation.conjunctionRight priorHi
  have nextLo := Derivation.conjunctionRight small
  have nextHi := Derivation.conjunctionRight large
  have low := exact_OpenSelectedGrammarSuccessorRow body α Γ lo old d H K m ids loTerms loArgs
    ⟨Derivation.conjunctionLeft priorLo⟩ ⟨Derivation.conjunctionLeft small⟩
    ⟨Derivation.conjunctionLeft prevLo⟩ ⟨Derivation.conjunctionRight prevLo⟩ loRange
  have high := exact_OpenSelectedGrammarSuccessorRow body α Γ hi next d H K M ids' hiTerms hiArgs
    ⟨Derivation.conjunctionLeft priorHi⟩ ⟨Derivation.conjunctionLeft large⟩
    ⟨Derivation.conjunctionLeft prevHi⟩ ⟨Derivation.conjunctionRight prevHi⟩ hiRange
  exact exact_OpenSelectedCoverSuccessorInclusion body α Γ old next oldTerms nextTerms oldArgs nextArgs
    H K ids ids' loTerms hiTerms loArgs hiArgs low high
    ⟨Derivation.conjunctionLeft nextLo⟩ ⟨Derivation.conjunctionLeft nextHi⟩
    ⟨Derivation.conjunctionRight nextLo⟩ ⟨Derivation.conjunctionRight nextHi⟩
    includeIds ⟨Derivation.conjunctionLeft prior⟩ ⟨Derivation.conjunctionRight prior⟩

private theorem withHighRange (d H K m M ids old oldTerms oldArgs next nextTerms nextArgs lo loTerms loArgs hi hiTerms hiArgs : OTerm α)
    (bound : Nonempty (Derivation body Γ (ltF m (suc M))))
    (ih : Nonempty (Derivation body Γ (widthAt d H K m M)))
    (small : Nonempty (Derivation body Γ (observed (suc d) H K m old oldTerms oldArgs)))
    (large : Nonempty (Derivation body Γ (observed (suc d) H K M next nextTerms nextArgs)))
    (priorLo : Nonempty (Derivation body Γ (observed d H K m lo loTerms loArgs)))
    (priorHi : Nonempty (Derivation body Γ (observed d H K M hi hiTerms hiArgs)))
    (loRange : Nonempty (Derivation body Γ (rangeReport ids (suc m)))) :
    Nonempty (Derivation body Γ (pairInclusion oldTerms nextTerms oldArgs nextArgs)) := by
  apply programCases ascendingRange ![suc M] _
  intro β j Δ idsNext keep actual
  simp only [unaryTapeRename,sucRelabel] at actual
  rw [pairRename]
  have b := renameInto bound j Δ keep
  have ih' := renameInto ih j Δ keep
  have s := renameInto small j Δ keep
  have l := renameInto large j Δ keep
  rw [orderRename,sucRelabel] at b
  rw [widthRename] at ih'
  rw [observedRename,sucRelabel] at s l
  have priorLo' := renameInto priorLo j Δ keep
  rw [observedRename] at priorLo'
  have priorHi' := renameInto priorHi j Δ keep
  rw [observedRename] at priorHi'
  have loRange' := renameInto loRange j Δ keep
  rw [rangeRename] at loRange'
  exact advanceWidth (d.relabel j) (H.relabel j) (K.relabel j) (m.relabel j) (M.relabel j) (ids.relabel j) idsNext
    (old.relabel j) (oldTerms.relabel j) (oldArgs.relabel j) (next.relabel j) (nextTerms.relabel j) (nextArgs.relabel j) (lo.relabel j) (loTerms.relabel j) (loArgs.relabel j) (hi.relabel j) (hiTerms.relabel j) (hiArgs.relabel j) b ih' loRange' actual priorLo' priorHi' s l

private theorem withLowRange (d H K m M old oldTerms oldArgs next nextTerms nextArgs lo loTerms loArgs hi hiTerms hiArgs : OTerm α)
    (bound : Nonempty (Derivation body Γ (ltF m (suc M))))
    (ih : Nonempty (Derivation body Γ (widthAt d H K m M)))
    (small : Nonempty (Derivation body Γ (observed (suc d) H K m old oldTerms oldArgs)))
    (large : Nonempty (Derivation body Γ (observed (suc d) H K M next nextTerms nextArgs)))
    (priorLo : Nonempty (Derivation body Γ (observed d H K m lo loTerms loArgs)))
    (priorHi : Nonempty (Derivation body Γ (observed d H K M hi hiTerms hiArgs))) :
    Nonempty (Derivation body Γ (pairInclusion oldTerms nextTerms oldArgs nextArgs)) := by
  apply programCases ascendingRange ![suc m] _
  intro β j Δ ids keep actual
  simp only [unaryTapeRename,sucRelabel] at actual
  rw [pairRename]
  have b := renameInto bound j Δ keep
  have ih' := renameInto ih j Δ keep
  have s := renameInto small j Δ keep
  have l := renameInto large j Δ keep
  rw [orderRename,sucRelabel] at b
  rw [widthRename] at ih'
  rw [observedRename,sucRelabel] at s l
  have priorLo' := renameInto priorLo j Δ keep
  rw [observedRename] at priorLo'
  have priorHi' := renameInto priorHi j Δ keep
  rw [observedRename] at priorHi'
  exact withHighRange (d.relabel j) (H.relabel j) (K.relabel j) (m.relabel j) (M.relabel j) ids (old.relabel j) (oldTerms.relabel j) (oldArgs.relabel j) (next.relabel j) (nextTerms.relabel j) (nextArgs.relabel j) (lo.relabel j) (loTerms.relabel j) (loArgs.relabel j) (hi.relabel j) (hiTerms.relabel j) (hiArgs.relabel j)
    b ih' s l priorLo' priorHi' actual

private theorem withHighPrior (d H K m M old oldTerms oldArgs next nextTerms nextArgs lo loTerms loArgs : OTerm α)
    (bound : Nonempty (Derivation body Γ (ltF m (suc M))))
    (ih : Nonempty (Derivation body Γ (widthAt d H K m M)))
    (small : Nonempty (Derivation body Γ (observed (suc d) H K m old oldTerms oldArgs)))
    (large : Nonempty (Derivation body Γ (observed (suc d) H K M next nextTerms nextArgs)))
    (priorLo : Nonempty (Derivation body Γ (observed d H K m lo loTerms loArgs))) :
    Nonempty (Derivation body Γ (pairInclusion oldTerms nextTerms oldArgs nextArgs)) := by
  apply observationCases d H K M _
  intro β j Δ hi hiTerms hiArgs keep actual
  rw [pairRename]
  have b := renameInto bound j Δ keep
  have ih' := renameInto ih j Δ keep
  have s := renameInto small j Δ keep
  have l := renameInto large j Δ keep
  rw [orderRename,sucRelabel] at b
  rw [widthRename] at ih'
  rw [observedRename,sucRelabel] at s l
  have priorLo' := renameInto priorLo j Δ keep
  rw [observedRename] at priorLo'
  exact withLowRange (d.relabel j) (H.relabel j) (K.relabel j) (m.relabel j) (M.relabel j) (old.relabel j) (oldTerms.relabel j) (oldArgs.relabel j) (next.relabel j) (nextTerms.relabel j) (nextArgs.relabel j) (lo.relabel j) (loTerms.relabel j) (loArgs.relabel j) hi hiTerms hiArgs
    b ih' s l priorLo' actual

private theorem withLowPrior (d H K m M old oldTerms oldArgs next nextTerms nextArgs : OTerm α)
    (bound : Nonempty (Derivation body Γ (ltF m (suc M))))
    (ih : Nonempty (Derivation body Γ (widthAt d H K m M)))
    (small : Nonempty (Derivation body Γ (observed (suc d) H K m old oldTerms oldArgs)))
    (large : Nonempty (Derivation body Γ (observed (suc d) H K M next nextTerms nextArgs))) :
    Nonempty (Derivation body Γ (pairInclusion oldTerms nextTerms oldArgs nextArgs)) := by
  apply observationCases d H K m _
  intro β j Δ lo loTerms loArgs keep actual
  rw [pairRename]
  have b := renameInto bound j Δ keep
  have ih' := renameInto ih j Δ keep
  have s := renameInto small j Δ keep
  have l := renameInto large j Δ keep
  rw [orderRename,sucRelabel] at b
  rw [widthRename] at ih'
  rw [observedRename,sucRelabel] at s l
  exact withHighPrior (d.relabel j) (H.relabel j) (K.relabel j) (m.relabel j) (M.relabel j) (old.relabel j) (oldTerms.relabel j) (oldArgs.relabel j) (next.relabel j) (nextTerms.relabel j) (nextArgs.relabel j) lo loTerms loArgs
    b ih' s l actual

theorem widthAtSuccessor (d H K m M : OTerm α)
    (bound : Nonempty (Derivation body Γ (ltF m (suc M))))
    (ih : Nonempty (Derivation body Γ (widthAt d H K m M))) :
    Nonempty (Derivation body Γ (widthAt (suc d) H K m M)) := by
  apply buildWidth (suc d) H K m M
  intro β j Δ old oldTerms oldArgs next nextTerms nextArgs keep small large
  have b := renameInto bound j Δ keep
  have prev := renameInto ih j Δ keep
  rw [orderRename,sucRelabel] at b
  rw [widthRename] at prev
  simp only [sucRelabel] at small large
  exact withLowPrior (d.relabel j) (H.relabel j) (K.relabel j) (m.relabel j) (M.relabel j)
    old oldTerms oldArgs next nextTerms nextArgs b prev small large

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthStepProof
