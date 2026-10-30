module

public import LogicLineages.ComputabilityKnowledge.GorbowFormulaSubstitution

@[expose] public section

/-! Literal standard-model instances in the existing full Gorbow language.
This reuses the accepted capture-avoiding substitution, unchanged. Context n
is ambient arity, not the source class of precisely n free variables. These
semantic suppliers cover substitution removing free variables as well.
Full closed L terms and closed arithmetic terms are kept distinct, matching
FS and the source untyped Barcan domain respectively. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowStandardInstances

open GorbowSyntax

def instantiate {n : Nat} (φ : Formula (n + 1)) (t : Term n) : Formula n :=
  GorbowFormulaSubstitution.substituteFormula (Fin.cases t Term.var) φ

def closedTermInContext (n : Nat) (t : Term 0) : Term n :=
  GorbowSubstitution.substitute Fin.elim0 t

inductive ArithmeticTerm : {n : Nat} → Term n → Prop where
  | var {n : Nat} (i : Fin n) : ArithmeticTerm (.var i)
  | zero {n : Nat} : ArithmeticTerm (.zero : Term n)
  | succ {n : Nat} {t : Term n} : ArithmeticTerm t → ArithmeticTerm (.succ t)
  | add {n : Nat} {t u : Term n} : ArithmeticTerm t → ArithmeticTerm u → ArithmeticTerm (.add t u)
  | mul {n : Nat} {t u : Term n} : ArithmeticTerm t → ArithmeticTerm u → ArithmeticTerm (.mul t u)

end LogicLineages.ComputabilityKnowledge.GorbowStandardInstances
