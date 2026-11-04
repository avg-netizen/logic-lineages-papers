module

public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticProgramDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProof

@[expose] public section
/-! Literal binder-correct bridge from the ordinary arithmetic graph compiler
into Gorbow's actual PA(L) syntax. No program/checker symbol is installed in
the language and no internal representation or HB theorem is assumed. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowOrdinaryArithmeticGraphs
open GorbowSyntax GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering

def translateTerm {alpha : Type} {m : Nat} (rho : alpha → Fin m) : OrdinaryArithmetic.Term alpha → Term m
  | .var i => .var (rho i)
  | .func .zero _ => .zero
  | .func .succ ts => .succ (translateTerm rho (ts 0))
  | .func .add ts => .add (translateTerm rho (ts 0)) (translateTerm rho (ts 1))
  | .func .mul ts => .mul (translateTerm rho (ts 0)) (translateTerm rho (ts 1))

/-- Mathlib bound variables are levels, with the NEW binder at last. Gorbow
uses de Bruijn indices, with the NEW binder at zero. The displayed map
explicitly implements this reversal at every quantifier. -/
def translateBounded {alpha : Type} : {l m : Nat} →
    OrdinaryArithmetic.arithmeticLanguage.BoundedFormula alpha l →
      (alpha → Fin m) → (Fin l → Fin m) → Formula m
  | _, _, .falsum, _, _ => .neg (.equal .zero .zero)
  | _, _, .equal t u, free, bound =>
      .equal (translateTerm (Sum.elim free bound) t) (translateTerm (Sum.elim free bound) u)
  | _, _, .rel r _, _, _ => nomatch r
  | _, _, .imp a b, free, bound =>
      .imp (translateBounded a free bound) (translateBounded b free bound)
  | _, _, .all a, free, bound => .all (translateBounded a
      (fun i => (free i).succ) (Fin.lastCases 0 (fun i => (bound i).succ)))

def graph {n : Nat} (p : Program n) : Formula (n + 1) :=
  translateBounded (OrdinaryArithmetic.graphFormula p) id Fin.elim0

/-- Visible arithmetic image, excluding U/u/Ag/K/T. -/
inductive ArithmeticFormula : {n : Nat} → Formula n → Prop where
  | equal {n : Nat} {s t : Term n} : GorbowStandardInstances.ArithmeticTerm s →
      GorbowStandardInstances.ArithmeticTerm t → ArithmeticFormula (.equal s t)
  | neg {n : Nat} {a : Formula n} : ArithmeticFormula a → ArithmeticFormula (.neg a)
  | imp {n : Nat} {a b : Formula n} : ArithmeticFormula a → ArithmeticFormula b →
      ArithmeticFormula (.imp a b)
  | all {n : Nat} {a : Formula (n+1)} : ArithmeticFormula a → ArithmeticFormula (.all a)

def closedGraph {n : Nat} (p : Program n) (inputs : List.Vector Nat n) (out : Nat) : Sentence :=
  GorbowFormulaSubstitution.substituteFormula
    (Fin.cases (Term.numeral out) (fun i => Term.numeral (inputs.get i))) (graph p)

end LogicLineages.ComputabilityKnowledge.GorbowOrdinaryArithmeticGraphs
