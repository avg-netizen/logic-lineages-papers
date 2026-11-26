module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCallProjectionProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof (call6)

theorem retainedPrior {α : Type} (k prior ctx ty start cert : OTerm α) :
    call6 k prior ctx ty start cert (1 : Fin 6) = prior := rfl

theorem retainedContext {α : Type} (k prior ctx ty start cert : OTerm α) :
    call6 k prior ctx ty start cert (2 : Fin 6) = ctx := rfl

theorem retainedType {α : Type} (k prior ctx ty start cert : OTerm α) :
    call6 k prior ctx ty start cert (3 : Fin 6) = ty := rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCallProjectionProof
