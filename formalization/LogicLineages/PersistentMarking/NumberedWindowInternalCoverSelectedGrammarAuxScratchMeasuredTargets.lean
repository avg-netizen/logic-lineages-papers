module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalAuxMeasureOpenTargets (measureGraph)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)

abbrev chosenMeasure (base : Program 1) : Program 1 :=
  selectedMeasure (measureUpdate base chosenCombine)

/-- Actual child grammar and own-key reports, at the scope read from
that child's actual selected measure. No universal child invariant. -/
structure MeasuredChild (base : Program 1) (s : Settings)
    (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (m depth width state terms args key : OTerm α) : Prop where
  measurement : Nonempty (Derivation body Γ (measureGraph base chosenCombine m key))
  code : Nonempty (Derivation body Γ (codePair m depth width))
  grammar : Nonempty (Derivation body Γ (observed depth (headsTerm s α) (typesTerm s α)
    width state terms args))
  occurs : Nonempty (Derivation body Γ (memberGraph terms key))

/-- For the actual selected measure and grammar, derive the tag-six
parent membership on the supplied original scratch. Parent measure,
scope pair, and four weak child bounds are conclusions of the checked
measurement row, not independent premises; the output and child
coordinates are tied to the same selected combine call. -/
def ExactOpenSelectedGrammarAuxScratchMeasured : Prop :=
  ∀ (V base : Program 1) (s : Settings) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α))
    (p mf ma df bf da ba fState fTerms fArgs aState aTerms aArgs vertices dom cod fn arg : OTerm α),
    MeasuredChild base s body Γ mf df bf fState fTerms fArgs fn →
    MeasuredChild base s body Γ ma da ba aState aTerms aArgs arg →
    Nonempty (Derivation body Γ (programGraph chosenCombine p ![mf,ma])) →
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) dom)) →
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) cod)) →
    Nonempty (Derivation body Γ (unary V (suc z) (auxiliaryTerm dom cod fn arg))) →
    Nonempty (Derivation body Γ
      (unary (scratchVertices (selectedCover V (chosenMeasure base)) s)
        vertices (auxiliaryTerm dom cod fn arg))) →
    Nonempty (Derivation body Γ (memberGraph vertices (auxiliaryTerm dom cod fn arg)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredTargets
