module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinMatchedPathTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredFormationRepresentativeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalThinMatchedCallsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalThinMatchedAdvanceChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalThinMatchedPathChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredOriginalMatchedPathProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFactoredCoverTargets (factoredCover)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (measuredFactoredExchange)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (window)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalThinMatchedCallsTargets (MatchedCallsAt)
open NumberedWindowInternalThinMatchedAdvanceTargets (MatchedAdvanceAt)
open NumberedWindowInternalThinMatchedPathTargets (MatchedPathAt)
open NumberedWindowInternalMeasuredFormationRepresentativeProof (exact_OriginalMeasuredFormationRepresentative)
open NumberedWindowInternalThinMatchedCallsChecks (exact_MatchedCalls)
open NumberedWindowInternalThinMatchedAdvanceChecks (exact_MatchedAdvance)
open NumberedWindowInternalThinMatchedPathChecks (exact_MatchedPath)

/-- Actual original finite-certificate matching through application on the
unrestricted measured physical tuple. Only the genuine ordinary formation,
original positive certificate and actual later application report are the
object antecedents. Different raw representatives at adjacent hops need
not coincide. This does not use an assumption of general Forward or a
numeric-to-open graph equality. -/
theorem exact_OriginalMeasuredMatchedPath (s : Settings) (base : Program 2)
    (V baseM : Program 1) (P : Program 2) (G baseW root other : Program 3) :
    let M := selectedMeasure (measureUpdate baseM P)
    let C := factoredCover V M G
    let W := window C s baseW V
    let X := measuredFactoredExchange s base V baseM P G
    let raw := typedRaw5 root other W V
    MatchedPathAt C X W s raw := by
  intro M C W X raw
  have rep := exact_OriginalMeasuredFormationRepresentative s base V baseM P G baseW
  have calls : MatchedCallsAt C X W s raw := exact_MatchedCalls C root other baseW X V s rep
  have step : MatchedAdvanceAt C X W s raw := exact_MatchedAdvance C X W s raw calls
  exact exact_MatchedPath C X W s raw step

#print axioms exact_OriginalMeasuredMatchedPath
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredOriginalMatchedPathProof
