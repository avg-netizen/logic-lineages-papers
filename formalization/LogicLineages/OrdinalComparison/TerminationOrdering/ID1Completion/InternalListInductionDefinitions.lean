module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInduction
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalClosedPrograms InternalListCodec SourceComputabilityFormulaSupportProof

/-- Substitute an arbitrary object-language code into a full-language invariant. -/
def atCode {α : Type} (theta : Formula (α ⊕ Fin 1))
    (n : OrdinaryArithmetic.Term α) : Formula α :=
  instantiate theta (arithmeticEmbedding.onTerm n)

/-- Preserve every free parameter and select one of the three bound codes.
The coordinates are the constructed code, its head, and its tail. -/
def atIndex {α : Type} (theta : Formula (α ⊕ Fin 1)) (i : Fin 3) :
    Formula (α ⊕ Fin 3) :=
  theta.relabel (Sum.elim Sum.inl (fun _ => Sum.inr i))

/-- The literal successor-of-pair constructor graph, with induction on its
tail. Neither canonicality nor an externally decoded list is assumed. -/
def constructorBody {α : Type} (theta : Formula (α ⊕ Fin 1)) :
    Formula (α ⊕ Fin 3) :=
  (programGraph consCode (.var (.inr 0))
    (Fin.cons (.var (.inr 1)) (Fin.cons (.var (.inr 2)) Fin.elim0))).imp
      ((atIndex theta 2).imp (atIndex theta 0))

def constructors {α : Type} (theta : Formula (α ⊕ Fin 1)) : Formula α :=
  allBlock (constructorBody theta)

def premises {α : Type} (theta : Formula (α ⊕ Fin 1)) : Formula α :=
  atCode theta OrdinaryArithmetic.zeroTerm ⊓ constructors theta

/-- List-code induction as one actual first-order theorem. The invariant may
contain the inductive predicate, arbitrary negation, and arbitrary parameters. -/
def schema {α : Type} (theta : Formula (α ⊕ Fin 1)) : Formula α :=
  (premises theta).imp (allOne theta)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInduction
