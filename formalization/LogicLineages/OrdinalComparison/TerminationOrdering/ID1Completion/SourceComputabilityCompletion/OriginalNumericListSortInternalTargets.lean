module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortInternalTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open SourceComputabilityFormulaSupportProof InternalApplicationCertificateConstructors
open InternalRawListRecursion OriginalNumericListSort
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal nil unfolding, arbitrary symbolic output and inserted value. -/
def InsertionStateNil : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (out : OTerm alpha) (x : OTerm alpha),
 Nonempty (Derivation body [] ((graph2 insertState out OrdinaryArithmetic.zeroTerm x).iff (programGraph insertBase out (Fin.cons x Fin.elim0))))

/-- Literal cons unfolding; no native evaluation or wellformedness premise. -/
def InsertionStateCons : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
 (code head tail out : OTerm alpha) (x : OTerm alpha),
 Nonempty (Derivation body [] ((graph2 InternalListCodec.consCode code head tail).imp
   ((graph2 insertState out code x).iff (consStep insertBase insertStep out head tail (Fin.cons x Fin.elim0)))))

/-- Literal nil unfolding, arbitrary symbolic output. -/
def SortNil : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (out : OTerm alpha),
 Nonempty (Derivation body [] ((graph1 sort out OrdinaryArithmetic.zeroTerm).iff (programGraph (zero : Program 0) out Fin.elim0)))

/-- Literal cons unfolding; no native evaluation or wellformedness premise. -/
def SortCons : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
 (code head tail out : OTerm alpha),
 Nonempty (Derivation body [] ((graph2 InternalListCodec.consCode code head tail).imp
   ((graph1 sort out code).iff (consStep (zero : Program 0) sortStep out head tail Fin.elim0))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortInternalTargets
