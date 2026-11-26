module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open SourceComputabilityFormulaSupportProof InternalApplicationCertificateConstructors
open InternalRawListRecursion OriginalNumericListSort
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalRawListRecursionProof

theorem insertionStateNil : OriginalNumericListSortInternalTargets.InsertionStateNil := by
 intro body alpha out x
 exact actualOriginalListRecursionZero body 1 insertBase insertStep alpha out (Fin.cons x Fin.elim0)

theorem insertionStateCons : OriginalNumericListSortInternalTargets.InsertionStateCons := by
 intro body alpha code head tail out x
 exact actualOriginalListRecursionCons body 1 insertBase insertStep alpha code head tail out (Fin.cons x Fin.elim0)

theorem sortNil : OriginalNumericListSortInternalTargets.SortNil := by
 intro body alpha out
 exact actualOriginalListRecursionZero body 0 (zero : Program 0) sortStep alpha out Fin.elim0

theorem sortCons : OriginalNumericListSortInternalTargets.SortCons := by
 intro body alpha code head tail out
 exact actualOriginalListRecursionCons body 0 (zero : Program 0) sortStep alpha code head tail out Fin.elim0

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortInternalProof
