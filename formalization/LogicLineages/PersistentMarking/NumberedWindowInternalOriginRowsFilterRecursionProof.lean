module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginRowsFilterTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginRowsFilterRecursionProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalRawListRecursionProof
  (actualOriginalListRecursionZero actualOriginalListRecursionCons)
open NumberedWindowInternalOriginRowsFilterTargets

theorem exact_OpenOriginRowFilterNil : ExactOpenOriginRowFilterNil := by
  intro side B α pool out
  exact actualOriginalListRecursionZero B 1 zeroBase (rowStep side) α out ![pool]

theorem exact_OpenOriginRowFilterCons : ExactOpenOriginRowFilterCons := by
  intro side B α code head tail pool out
  exact actualOriginalListRecursionCons B 1 zeroBase (rowStep side) α code head tail out ![pool]

#print axioms exact_OpenOriginRowFilterNil
#print axioms exact_OpenOriginRowFilterCons

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginRowsFilterRecursionProof
