module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalRecursionGraph

def ActualOriginalRecursionInstance : Prop :=
  ∀ (n : Nat) (α : Type) (f : OFormula (Fin (n + 1))) (g : OFormula (Fin (n + 3)))
    (out t : OTerm α) (xs : Fin n → OTerm α),
  recursion f g out t xs = InternalFiniteBlocks.block
    (arithmeticEmbedding.onFormula (InternalRecursionGraph.matrix f g out t xs))

/-- No totality or functionality assumptions on either arithmetic relation. -/
def ActualOriginalRecursionZeroElimination : Prop :=
  ∀ (body : Positive (Fin 1)) (n : Nat) (α : Type)
    (f : OFormula (Fin (n + 1))) (g : OFormula (Fin (n + 3)))
    (out : OTerm α) (xs : Fin n → OTerm α),
  Nonempty (Derivation body []
    ((recursion f g out OrdinaryArithmetic.zeroTerm xs).imp (graph f out xs)))

def ActualOriginalRecursionSuccessorElimination : Prop :=
  ∀ (body : Positive (Fin 1)) (n : Nat) (α : Type)
    (f : OFormula (Fin (n + 1))) (g : OFormula (Fin (n + 3)))
    (out t : OTerm α) (xs : Fin n → OTerm α),
  Nonempty (Derivation body []
    ((recursion f g out (OrdinaryArithmetic.succTerm t) xs).imp
      (successorStep f g out t xs)))

def ActualOriginalRecursionZeroIntroduction : Prop :=
  ∀ (body : Positive (Fin 1)) (n : Nat) (α : Type)
    (f : OFormula (Fin (n + 1))) (g : OFormula (Fin (n + 3)))
    (out : OTerm α) (xs : Fin n → OTerm α),
  Nonempty (Derivation body []
    ((graph f out xs).imp (recursion f g out OrdinaryArithmetic.zeroTerm xs)))

def ActualOriginalRecursionSuccessorIntroduction : Prop :=
  ∀ (body : Positive (Fin 1)) (n : Nat) (α : Type)
    (f : OFormula (Fin (n + 1))) (g : OFormula (Fin (n + 3)))
    (out t : OTerm α) (xs : Fin n → OTerm α),
  Nonempty (Derivation body []
    ((successorStep f g out t xs).imp
      (recursion f g out (OrdinaryArithmetic.succTerm t) xs)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphTargets
