module
public import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementReportTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementReportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementReportChecks
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.SourcePresentation (sourceBody)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalPositiveEndpointRefinement (withEndpointCarriers)
open NumberedWindowInternalPositiveEndpointRefinementReportTargets
open NumberedWindowInternalPositiveEndpointRefinementReportProof (openReport)

theorem exact_OpenEndpointRefinedReport : ExactOpenEndpointRefinedReport := openReport

theorem exact_InstalledEndpointRefinedReport : ExactInstalledEndpointRefinedReport := by
  intro i j cv tv d raw least c α left witness right
  let r := withEndpointCarriers i (addressPositive cv tv raw least)
  exact openReport i cv tv raw least (sourceBody (data i j r d) c) α [] left witness right

#print axioms exact_OpenEndpointRefinedReport
#print axioms exact_InstalledEndpointRefinedReport

end LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementReportChecks
