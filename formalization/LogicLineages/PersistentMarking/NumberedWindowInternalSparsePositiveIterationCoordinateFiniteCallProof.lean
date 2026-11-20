module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateFinitePureProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateThinGraphProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateFiniteCallProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof (call6)
open NumberedWindowInternalSparsePositiveIterationCoordinateThinGraphProof (retained)
open NumberedWindowInternalSparsePositiveIterationCoordinateFinitePureProof (retainedEqual)

/-- Whole source call6 families agree at the three truly retained fields.
The only actual tuple computations here are the three literal projections. -/
theorem sameRetained {α : Type} (k prior c ty start cert k' start' cert' : OTerm α)
    (i : Fin 6) (keep : retained i) :
    call6 k prior c ty start cert i = call6 k' prior c ty start' cert' i :=
  retainedEqual (call6 k prior c ty start cert) (call6 k' prior c ty start' cert')
    rfl rfl rfl i keep

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateFiniteCallProof
