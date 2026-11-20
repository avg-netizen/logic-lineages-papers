module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleReportProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.SourcePresentation (sourceBody)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseAddressPositiveOpenChecks (exact_OpenAddressPositive)
open NumberedWindowInternalSparseTupleTargets

theorem installed : ExactInstalledPositiveReport := by
  intro i j cv tv d raw least c α left cert right
  exact exact_OpenAddressPositive (sourceBody (data i j (addressPositive cv tv raw least) d) c)
    cv tv raw least α left cert right

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleReportProof
