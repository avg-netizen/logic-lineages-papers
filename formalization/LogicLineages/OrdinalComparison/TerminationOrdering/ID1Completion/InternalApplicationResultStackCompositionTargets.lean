module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalGraphComposition
open InternalApplicationCertificateConstructors InternalApplicationResultStackComposition
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Empty work fixes the entire encoded state at every symbolic count. The
arbitrary result stack is retained literally, rather than replaced by a
Boolean success constant or restricted to a singleton output. -/
def ActualOriginalResultStackTerminalIteration : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 1) (combine : Program 4) (α : Type)
    (count results state out : OTerm α),
  Nonempty (Derivation body []
    ((graph1 InternalApplicationResultStack.emptyState state results).imp
      ((graph2 (InternalApplicationResultStack.iterate guard leaf combine) out count state).iff
        (equal out state))))

/-- At zero steps, success means exactly empty initial work and equality of
whole result stacks. The statement is internal and preserves raw symbolic
codes; it does not appeal to standard-model decoding or evaluation. -/
def ActualOriginalResultStackRunZero : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 1) (combine : Program 4) (α : Type)
    (work initialResults finalResults : OTerm α),
  Nonempty (Derivation body []
    ((actualRun guard leaf combine OrdinaryArithmetic.zeroTerm work initialResults finalResults).iff
      (equal work OrdinaryArithmetic.zeroTerm ⊓ equal finalResults initialResults)))

/-- Successful sequential composition preserves the exact final results of
the second computation. Each run may include terminal padding, so this does
NOT assert that the suffix is untouched after the first stated count. All
counts and work/result stacks are arbitrary symbolic original raw codes. -/
def ActualOriginalResultStackWorkAppend : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 1) (combine : Program 4) (α : Type)
    (first second frontWork suffix joined initialResults middleResults finalResults : OTerm α),
  Nonempty (Derivation body []
    ((graph2 InternalApplicationValidityStackAppend.append joined frontWork suffix ⊓
      (actualRun guard leaf combine first frontWork initialResults middleResults ⊓
        actualRun guard leaf combine second suffix middleResults finalResults)).imp
      (actualRun guard leaf combine (OrdinaryArithmetic.addTerm first second)
        joined initialResults finalResults)))

/-- Append the same arbitrary background to BOTH result stacks of a
successful run. The worklist and exact count do not change. Successful
execution rules out any failed underflow, so this does not claim a framing
law for arbitrary failed transitions or for runs with different statuses. -/
def ActualOriginalResultStackResultSuffixFrame : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 1) (combine : Program 4) (α : Type)
    (count work initialResults finalResults background framedInitial framedFinal : OTerm α),
  Nonempty (Derivation body []
    ((actualRun guard leaf combine count work initialResults finalResults ⊓
      (graph2 InternalApplicationValidityStackAppend.append framedInitial initialResults background ⊓
        graph2 InternalApplicationValidityStackAppend.append framedFinal finalResults background)).imp
      (actualRun guard leaf combine count work framedInitial framedFinal)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionTargets
