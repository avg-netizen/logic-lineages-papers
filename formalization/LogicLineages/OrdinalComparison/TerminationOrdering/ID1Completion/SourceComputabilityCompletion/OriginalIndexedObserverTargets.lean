module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open OriginalIndexedObserverDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Generic proof-side constructor induction, scoped to actual context range.
No specific observer or selected final tuple is asserted to satisfy the laws.
Lambda visits use successor cutoff in their actual extended parameter. -/
def ActualIndexedObserverTraversal : Prop :=
  ∀ (data : Data) (window : Program 1) (K : Program 3),
  ApplicationLaw data window K → LambdaLaw data window K → OtherLaw data window K →
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter mark cutoff : OrdinaryArithmetic.Term alpha),
  Nonempty (Derivation body Delta
    ((premises data window out input typ parameter ⊓ ActualRange cutoff parameter).imp
      (observations K out input parameter mark cutoff)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverTargets
