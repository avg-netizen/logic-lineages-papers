module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarCrossBoundTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthBaseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverObjectInclusionTransitivityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarCrossBoundProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalOriginalOrderSyntaxProof (orderRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open NumberedWindowInternalCoverSelectedGrammarWidthObservationProof (observationCases)
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedRename)
open NumberedWindowInternalCoverSelectedGrammarDepthBaseProof (inclusionRename)
open NumberedWindowInternalCoverSelectedGrammarWidthInductionProof (exact_OpenSelectedGrammarWidth)
open NumberedWindowInternalCoverSelectedGrammarWeakDepthInductionProof (exact_OpenSelectedGrammarWeakDepth)
open NumberedWindowInternalCoverObjectInclusionTransitivityProof (composePair)
open NumberedWindowInternalCoverSelectedGrammarCrossBoundTargets

theorem exact_OpenSelectedGrammarCrossBound : ExactOpenSelectedGrammarCrossBound := by
  intro body α Γ d D H K m M old oldTerms oldArgs next nextTerms nextArgs depth width small large
  apply observationCases d H K M _
  intro β j Δ mid midTerms midArgs keep actual
  rw [inclusionRename]
  have d' := renameInto depth j Δ keep
  have m' := renameInto width j Δ keep
  rw [orderRename,sucRelabel] at d' m'
  have old' := renameInto small j Δ keep
  have next' := renameInto large j Δ keep
  rw [observedRename] at old' next'
  have first := exact_OpenSelectedGrammarWidth body β Δ
    (d.relabel j) (H.relabel j) (K.relabel j) (m.relabel j) (M.relabel j)
    (old.relabel j) (oldTerms.relabel j) (oldArgs.relabel j) mid midTerms midArgs
    m' old' actual
  have last := exact_OpenSelectedGrammarWeakDepth body β Δ
    (d.relabel j) (D.relabel j) (H.relabel j) (K.relabel j) (M.relabel j)
    mid midTerms midArgs (next.relabel j) (nextTerms.relabel j) (nextArgs.relabel j)
    d' actual next'
  exact composePair body β Δ (oldTerms.relabel j) midTerms (nextTerms.relabel j)
    (oldArgs.relabel j) midArgs (nextArgs.relabel j) first last

#print axioms exact_OpenSelectedGrammarCrossBound

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarCrossBoundProof
