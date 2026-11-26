module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateThinGraphProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateAbstractTupleProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof (call6)
open NumberedWindowInternalSparsePositiveIterationCoordinateThinGraphProof (retained)

/-- Pure tuple bookkeeping only. The six terms are the fixed source call6
coordinates; no arithmetic formula or Program AST is unfolded here. -/
theorem sameRetained {α : Type} (k prior c ty start cert k' start' cert' : OTerm α)
    (i : Fin 6) (keep : retained i) :
    call6 k prior c ty start cert i = call6 k' prior c ty start' cert' i := by
  unfold retained at keep
  rcases keep with hit | hit | hit
  all_goals rw [hit] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateAbstractTupleProof
