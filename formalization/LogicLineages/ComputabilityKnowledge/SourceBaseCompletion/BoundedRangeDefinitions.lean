module

public import LogicLineages.ComputabilityKnowledge.GorbowOrdinaryArithmeticGraphsDefinitions

@[expose] public section
/-! Literal fixed finite bounds for the existing ordinary arithmetic graph
compiler. All retained parameters and arbitrary full-language matrices are
preserved. These are PA formulas and proof targets, never added axioms. -/
namespace LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.BoundedRange
open GorbowSyntax
open LogicLineages.OrdinalComparison.TerminationOrdering

def ordinaryNumeral {alpha : Type} : Nat → OrdinaryArithmetic.Term alpha
  | 0 => OrdinaryArithmetic.zeroTerm
  | n + 1 => OrdinaryArithmetic.succTerm (ordinaryNumeral n)

/-- The EXACT translated strict-bound formula emitted by the paid compiler.
Only the guard's free index0 is mapped to the newest current parameter. -/
def guard {m : Nat} (bound : Nat) : Formula (m+1) :=
  GorbowFormulaSubstitution.substituteFormula (fun _ : Fin 1 => (.var 0 : Term (m+1)))
    (GorbowOrdinaryArithmeticGraphs.translateBounded
      (OrdinaryArithmetic.lessFormula (.var (0 : Fin 1)) (ordinaryNumeral bound))
      id Fin.elim0)

/-- Visible implication/falsum encoding of exists d, x+S(d)=bound. -/
def literalGuard {m : Nat} (bound : Nat) : Formula (m+1) :=
  .imp (.all (.imp
    (.equal (.add (.var 1) (.succ (.var 0))) (Term.numeral bound))
    (.neg (.equal .zero .zero)))) (.neg (.equal .zero .zero))

def casesBelow {m : Nat} (bound : Nat) : Formula (m+1) :=
  (List.ofFn (fun i : Fin bound =>
    (Formula.equal (.var 0) (Term.numeral i.val) : Formula (m+1)))).foldr
      Formula.disj (.neg (.equal .zero .zero))

def bounded {m : Nat} (bound : Nat) (phi : Formula (m+1)) : Formula m :=
  .all (.imp (guard bound) phi)

end LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.BoundedRange
