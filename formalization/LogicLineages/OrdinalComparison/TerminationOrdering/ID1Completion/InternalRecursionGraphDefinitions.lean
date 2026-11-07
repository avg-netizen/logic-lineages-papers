module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraph
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open SourceComputabilityFormulaSupportProof

/-- The literal original compiled recursion graph. Its counter is the first
input; all remaining inputs preserve their original names and order. -/
def recursion {n : Nat} {α : Type} (f : OFormula (Fin (n + 1)))
    (g : OFormula (Fin (n + 3))) (out t : OTerm α) (xs : Fin n → OTerm α) : Formula α :=
  graph (OrdinaryArithmetic.recursionGraph f g) out (Fin.cons t xs)

/-- The original existential code-pair matrix at arbitrary term instances. -/
def matrix {n : Nat} {α : Type} (f : OFormula (Fin (n + 1)))
    (g : OFormula (Fin (n + 3))) (out t : OTerm α) (xs : Fin n → OTerm α) :
    OFormula (α ⊕ Fin 2) :=
  let a : OTerm (α ⊕ Fin 2) := .var (.inr 0)
  let b : OTerm (α ⊕ Fin 2) := .var (.inr 1)
  let params := fun i => (xs i).relabel Sum.inl
  (OrdinaryArithmetic.initialGraph f a b params ⊓
    OrdinaryArithmetic.stepGraph g a b (t.relabel Sum.inl) params) ⊓
    OrdinaryArithmetic.betaFormula a b (t.relabel Sum.inl) (out.relabel Sum.inl)

/-- The defining successor equation retains the evaluator's exact order:
output, previous counter, previous result, then original parameters. -/
def successorStep {n : Nat} {α : Type} (f : OFormula (Fin (n + 1)))
    (g : OFormula (Fin (n + 3))) (out t : OTerm α) (xs : Fin n → OTerm α) : Formula α :=
  existsOne (recursion f g (.var (.inr (0 : Fin 1))) (t.relabel Sum.inl)
      (fun i => (xs i).relabel Sum.inl) ⊓
    graph g (out.relabel Sum.inl) (Fin.cons (t.relabel Sum.inl)
      (Fin.cons (.var (.inr 0)) (fun i => (xs i).relabel Sum.inl))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraph
