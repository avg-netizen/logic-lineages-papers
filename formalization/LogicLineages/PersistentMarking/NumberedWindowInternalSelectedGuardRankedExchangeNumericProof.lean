module
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredExchangeNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalTransparentAuxRankNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineDefinitions

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionTargets
public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSelectedGuardRankedExchangeNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScalarEdge (exchangeTape)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated factoredCover)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxExchangeMemoStepTargets (step)
open NumberedWindowInternalAuxExchangeMemoTargets (selected)
open NumberedWindowInternalMeasuredExchangeThinDefinitions (measuredExchange)
open NumberedWindowInternalMeasuredExchangeThinNumericProof (exact_LiteralMeasuredExchangeCalibration)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof
open NumberedWindowInternalRankMeasuredExchange (rankedExchange)
open NumberedWindowInternalRankMeasuredExchangeNumericProof (exact_RankMeasuredFactoredCalibration)
open NumberedWindowInternalTransparentAuxRankTargets (RankCalibrated auxRank)
open NumberedWindowInternalTransparentAuxRankNumericProof (exact_TransparentAuxRankCalibration)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntax)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalCoverSelectedGrammarOptionTargets (selectedGrammarOption)

/-- Insert the real transparent auxiliary rank equality before the
paired/cover guard without changing the ordinary original exchange
bit on any input. This is a numerical correspondence, not a
reflection premise for a symbolic derivation. -/
theorem exact_OriginalSelectedGuardRankedExchangeNumeric
    (s : Settings) (base : Program 2) (V TV baseM g : Program 1) :
    let Va := auxSyntax V TV
    let M := selectedMeasure (measureUpdate baseM chosenCombine)
    let C := factoredCover Va M selectedGrammarOption
    let D := selected (step base Va)
    RankCalibrated g →
    TermMeasureCalibrated M →
    ActualTermExchange s D →
    HeadPairsSymmetric s.equivalentHeads →
    ActualSelectedCoverOutput C →
    ∀ a b, evaluate (rankedExchange C s (auxRank g) (measuredExchange M D))
        (List.Vector.ofFn (exchangeTape a b)) =
      evaluate (measuredFactoredExchange s base Va baseM chosenCombine selectedGrammarOption)
        (List.Vector.ofFn (exchangeTape a b)) := by
  intro Va M C D fit measure directed symmetry cover a b
  have m := exact_LiteralMeasuredExchangeCalibration s M D measure directed
  have r := exact_RankMeasuredFactoredCalibration C s (auxRank g) (measuredExchange M D)
    (exact_TransparentAuxRankCalibration g fit) m symmetry cover
  have ordinary := exact_LiteralMeasuredFactoredCalibration
    s base Va baseM chosenCombine selectedGrammarOption symmetry cover measure directed
  exact (r a b).trans (ordinary a b).symm

#print axioms exact_OriginalSelectedGuardRankedExchangeNumeric
end LogicLineages.PersistentMarking.NumberedWindowInternalSelectedGuardRankedExchangeNumericProof
