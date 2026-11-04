module

public import LogicLineages.ComputabilityKnowledge.GorbowOrdinaryArithmeticGraphsDefinitions

@[expose] public section
/-! Internal Hilbert graph certificates, using the exact ordinary-arithmetic
compiler and its literal Gorbow translation. No semantic-to-proof inference,
graph-correctness axiom, program symbol or internal HB premise is introduced. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowArithmeticCompositionCertificates
open GorbowSyntax GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering

def falseFormula {n : Nat} : Formula n := .neg (.equal .zero .zero)

/-- The exact implication/falsum encoding of Mathlib's existential. -/
def encodedExists (a : Formula 1) : Sentence :=
  .imp (.all (.imp a falseFormula)) falseFormula

def closedArithmetic {n : Nat} (a : OrdinaryArithmetic.Formula (Fin n))
    (v : Fin n → Nat) : Sentence :=
  GorbowFormulaSubstitution.substituteFormula (fun i => Term.numeral (v i))
    (GorbowOrdinaryArithmeticGraphs.translateBounded a id Fin.elim0)

/-- The genuine zero/successor/projection/composition fragment of the SAME
Program AST. The recursion constructor is explicitly excluded. -/
def recursionFree : {n : Nat} → Program n → Prop
  | _, .zero => True
  | _, .succ => True
  | _, .projection _ => True
  | _, .composition f g => recursionFree f ∧ ∀ i, recursionFree (g i)
  | _, .recursion _ _ => False

end LogicLineages.ComputabilityKnowledge.GorbowArithmeticCompositionCertificates
