module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaInvariantDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSliceInduction
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticTransforms
open InternalCalculus SourceEndpoint SourceComputabilityFormulaSupportProof

/-- The original untagged scalar or multiset operator, with the same closed
context numeral as the one combined source body. This is syntax for a closure
premise; it does not introduce a second inductive definition. -/
def sliceBody (data : SourcePresentation.Data) (context : Nat) (odd : Bool) : Positive (Fin 1) :=
  substitutePositive ![numeral context,.var 0]
    (if odd then SourcePresentation.multisetOperator data
      else SourcePresentation.scalarOperator data)

/-- The original predicate at an even or odd tag, with its object variable
free. This invariant leaves the unselected slice unchanged. -/
def currentSlice {α : Type} (odd : Bool) : Formula (α ⊕ Fin 1) :=
  (Positive.predicate (tagTerm odd (.var (.inr (0 : Fin 1))))).formula

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSliceInduction
