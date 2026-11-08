module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackComposition
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalGraphComposition
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Inputs [work,results]. This is the literal original nested-pair state
constructor with status one, using the unchanged arbitrary raw list codes. -/
def liveState : Program 2 :=
  InternalApplicationResultStack.liveOf (.projection 0) (.projection 1)

/-- Success after the stated count in the ACTUAL numeric result-stack AST,
retaining both the entire initial and final result stacks. The outer witness
is the initial state; the inner witness is the final empty-work live state.
Both are constrained by concrete original pair-constructor program graphs.
No external execution, decoder, validity or result-shape premise is hidden
here. In particular the final state depends on finalResults, not a constant.
An early completion may consume unused empty-work fixed-point fuel. -/
def actualRun {α : Type} (guard leaf : Program 1) (combine : Program 4)
    (count work initialResults finalResults : OTerm α) : Formula α :=
  existsOne
    (graph2 liveState (.var (.inr (0 : Fin 1)))
        (work.relabel Sum.inl) (initialResults.relabel Sum.inl) ⊓
      existsOne
        (graph1 InternalApplicationResultStack.emptyState (.var (.inr (0 : Fin 1)))
            ((finalResults.relabel Sum.inl).relabel Sum.inl) ⊓
          graph2 (InternalApplicationResultStack.iterate guard leaf combine)
            (.var (.inr (0 : Fin 1))) ((count.relabel Sum.inl).relabel Sum.inl)
            (.var (.inl (.inr (0 : Fin 1))))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackComposition
