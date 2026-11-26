module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinMatchedPathTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredFormationRepresentativeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalThinMatchedCallsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalThinMatchedAdvanceChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalThinMatchedPathChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredMatchedPathProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFactoredCoverTargets (factoredCover)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalRankMeasuredExchange (rankedExchange)
open NumberedWindowInternalMeasuredExchangeThinDefinitions (measuredExchange)
open NumberedWindowInternalAuxExchangeMemoStepTargets (step)
open NumberedWindowInternalAuxExchangeMemoTargets (selected)
open NumberedWindowInternalTransparentAuxRankTargets (auxRank)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (window)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalThinMatchedCallsTargets (MatchedCallsAt)
open NumberedWindowInternalThinMatchedAdvanceTargets (MatchedAdvanceAt)
open NumberedWindowInternalThinMatchedPathTargets (MatchedPathAt)
open NumberedWindowInternalRankMeasuredFormationRepresentativeProof (exact_OriginalRankMeasuredFormationRepresentative)
open NumberedWindowInternalThinMatchedCallsChecks (exact_MatchedCalls)
open NumberedWindowInternalThinMatchedAdvanceChecks (exact_MatchedAdvance)
open NumberedWindowInternalThinMatchedPathChecks (exact_MatchedPath)

/-- Actual original finite-certificate matching through application on the
rank-tested measured physical tuple. Only the genuine ordinary formation,
original positive certificate and actual later application report are the
object antecedents. Different raw representatives at adjacent hops need
not coincide. This does not use an assumption of general Forward or a
numeric-to-open graph equality. -/
theorem exact_OriginalRankMeasuredMatchedPath (s : Settings) (base : Program 2)
    (V baseM g : Program 1) (P : Program 2) (G baseW root other : Program 3) :
    let M := selectedMeasure (measureUpdate baseM P)
    let C := factoredCover V M G
    let W := window C s baseW V
    let R := auxRank g
    let D := measuredExchange M (selected (step base V))
    let X := rankedExchange C s R D
    let raw := typedRaw5 root other W V
    MatchedPathAt C X W s raw := by
  intro M C W R D X raw
  have rep := exact_OriginalRankMeasuredFormationRepresentative s base V baseM g P G baseW
  have calls : MatchedCallsAt C X W s raw := exact_MatchedCalls C root other baseW X V s rep
  have advance : MatchedAdvanceAt C X W s raw := exact_MatchedAdvance C X W s raw calls
  exact exact_MatchedPath C X W s raw advance

#print axioms exact_OriginalRankMeasuredMatchedPath
end LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredMatchedPathProof
