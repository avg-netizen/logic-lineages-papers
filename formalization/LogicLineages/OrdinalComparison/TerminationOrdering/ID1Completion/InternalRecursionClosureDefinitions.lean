module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosure
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalRecursionGraph
open SourceComputabilityFormulaSupportProof

/-- Existence at an arbitrary object-language counter, with the output bound. -/
def totalAt {n : Nat} {α : Type} (f : OFormula (Fin (n+1)))
    (g : OFormula (Fin (n+3))) (t : OTerm α) (xs : Fin n → OTerm α) : Formula α :=
  existsOne (recursion f g (.var (.inr (0 : Fin 1))) (t.relabel Sum.inl)
    (fun i => (xs i).relabel Sum.inl))

/-- Both outputs are bound inside the induction formula. Parameters and the
counter retain their original free names. No existence premise is present. -/
def uniqueAt {n : Nat} {α : Type} (f : OFormula (Fin (n+1)))
    (g : OFormula (Fin (n+3))) (t : OTerm α) (xs : Fin n → OTerm α) : Formula α :=
  InternalClosedPrograms.allBlock
    ((recursion f g (.var (.inr (0 : Fin 2))) (t.relabel Sum.inl)
        (fun i => (xs i).relabel Sum.inl) ⊓
      recursion f g (.var (.inr 1)) (t.relabel Sum.inl)
        (fun i => (xs i).relabel Sum.inl)).imp
      (arithmeticEmbedding.onFormula
        ((Term.var (.inr (0 : Fin 2)) : OTerm (α ⊕ Fin 2)).equal (.var (.inr 1)))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosure
