module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackComposition
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalGraphComposition
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Success after the stated count in the ACTUAL parameterized result-stack
iterator. Both witnesses use the unchanged original state constructors:
liveState [work,initialResults] and emptyState [finalResults]. The entire
final result stack is retained, not replaced by a Boolean completion code.
The same arbitrary symbolic parameter is weakened through both binders and
passed only as the last iterator input. It is not existentially selected,
inserted into either original state, or used to change count or fuel.
Early completion may consume unused empty-work fixed-point steps. -/
def actualRunP {α : Type} (guard leaf : Program 2) (combine : Program 5)
    (count work initialResults finalResults parameter : OTerm α) : Formula α :=
  existsOne
    (graph2 InternalApplicationResultStackComposition.liveState (.var (.inr (0 : Fin 1)))
        (work.relabel Sum.inl) (initialResults.relabel Sum.inl) ⊓
      existsOne
        (graph1 InternalApplicationResultStack.emptyState (.var (.inr (0 : Fin 1)))
            ((finalResults.relabel Sum.inl).relabel Sum.inl) ⊓
          graph3 (InternalParameterizedApplicationResultStack.iterateP guard leaf combine)
            (.var (.inr (0 : Fin 1))) ((count.relabel Sum.inl).relabel Sum.inl)
            (.var (.inl (.inr (0 : Fin 1))))
            ((parameter.relabel Sum.inl).relabel Sum.inl)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackComposition
