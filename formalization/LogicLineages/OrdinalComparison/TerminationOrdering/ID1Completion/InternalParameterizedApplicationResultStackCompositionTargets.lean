module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalGraphComposition
open InternalApplicationCertificateConstructors InternalParameterizedApplicationResultStackComposition
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- At zero steps, actual success at the arbitrary symbolic parameter means
exactly empty original work and equality of the entire final and initial
result stacks. No evaluation, validity or completion predicate is assumed. -/
def ActualOriginalParameterizedResultStackRunZero : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 2) (combine : Program 5) (α : Type)
    (Gamma : List (Formula α)) (work initialResults finalResults parameter : OTerm α),
  Nonempty (Derivation body Gamma
    ((actualRunP guard leaf combine OrdinaryArithmetic.zeroTerm
        work initialResults finalResults parameter).iff
      (equal work OrdinaryArithmetic.zeroTerm ⊓ equal finalResults initialResults)))

/-- Successful original work composition at ONE identical symbolic
parameter. The first actual run returns the whole middle result stack,
which is the second run's whole initial stack. The final count is the
literal arithmetic first+second and the actual final results are preserved.
Terminal padding is allowed; no untouched-suffix claim at first is made. -/
def ActualOriginalParameterizedResultStackWorkAppend : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 2) (combine : Program 5) (α : Type)
    (Gamma : List (Formula α))
    (first second frontWork suffix joined initialResults middleResults finalResults parameter : OTerm α),
  Nonempty (Derivation body Gamma
    ((graph2 InternalApplicationValidityStackAppend.append joined frontWork suffix ⊓
      (actualRunP guard leaf combine first frontWork initialResults middleResults parameter ⊓
        actualRunP guard leaf combine second suffix middleResults finalResults parameter)).imp
      (actualRunP guard leaf combine (OrdinaryArithmetic.addTerm first second)
        joined initialResults finalResults parameter)))

/-- Append the SAME arbitrary result background to both result stacks of
an ACTUAL successful run, preserving work, count and symbolic parameter.
Success excludes original failed underflow internally. There is no framing
claim for arbitrary failed runs and no added result-shape premise. -/
def ActualOriginalParameterizedResultStackResultSuffixFrame : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 2) (combine : Program 5) (α : Type)
    (Gamma : List (Formula α))
    (count work initialResults finalResults background framedInitial framedFinal parameter : OTerm α),
  Nonempty (Derivation body Gamma
    ((actualRunP guard leaf combine count work initialResults finalResults parameter ⊓
      (graph2 InternalApplicationValidityStackAppend.append framedInitial initialResults background ⊓
        graph2 InternalApplicationValidityStackAppend.append framedFinal finalResults background)).imp
      (actualRunP guard leaf combine count work framedInitial framedFinal parameter)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionTargets
