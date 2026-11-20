module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCallProjectionProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateFinitePureProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateThinGraphProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateExplicitCallProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof (call6)
open NumberedWindowInternalSparsePositiveIterationCoordinateThinGraphProof (retained)
open NumberedWindowInternalSparsePositiveIterationCoordinateFinitePureProof (retainedEqual)
open NumberedWindowInternalSparsePositiveIterationCallProjectionProof
  (retainedPrior retainedContext retainedType)

theorem sameRetained {α : Type} (k prior c ty start cert k' start' cert' : OTerm α)
    (i : Fin 6) (keep : retained i) :
    call6 k prior c ty start cert i = call6 k' prior c ty start' cert' i :=
  retainedEqual (X := OTerm α) (call6 k prior c ty start cert) (call6 k' prior c ty start' cert')
    (Eq.trans (retainedPrior k prior c ty start cert)
      (Eq.symm (retainedPrior k' prior c ty start' cert')))
    (Eq.trans (retainedContext k prior c ty start cert)
      (Eq.symm (retainedContext k' prior c ty start' cert')))
    (Eq.trans (retainedType k prior c ty start cert)
      (Eq.symm (retainedType k' prior c ty start' cert')))
    i (show i = 1 ∨ i = 2 ∨ i = 3 from keep)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateExplicitCallProof
