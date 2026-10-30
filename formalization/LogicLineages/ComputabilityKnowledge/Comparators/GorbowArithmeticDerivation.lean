module

public import LogicLineages.ComputabilityKnowledge.GorbowArithmeticDerivation

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowArithmeticDerivation
open GorbowSyntax GorbowStandardInstances
open LogicLineages.ComputabilityKnowledge.GorbowArithmeticDerivation

def NumeralAddition : Prop := ∀ a b,
  Calculation (.add (Term.numeral a) (Term.numeral b)) (a+b)

def NumeralMultiplication : Prop := ∀ a b,
  Calculation (.mul (Term.numeral a) (Term.numeral b)) (a*b)

def ClosedEvaluation : Prop := ∀ (t : Term 0), ArithmeticTerm t → ∀ I,
  Calculation t (t.realize I Fin.elim0)

def EqualValues : Prop := ∀ (t u : Term 0), ArithmeticTerm t → ArithmeticTerm u → ∀ I,
  t.realize I Fin.elim0=u.realize I Fin.elim0 → Nonempty (GorbowPACore.Proof (.equal t u))

def Target : Prop := NumeralAddition ∧ NumeralMultiplication ∧ ClosedEvaluation ∧ EqualValues
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowArithmeticDerivation
