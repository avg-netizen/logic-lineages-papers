module

public import LogicLineages.ComputabilityKnowledge.GorbowArithmeticCompositionCertificatesDefinitions

@[expose] public section
/-! Concrete internal beta-sequence certificates for the ACTUAL ordinary
arithmetic formula. The two code components remain separate arithmetic
variables; no beta/program/pairing symbol or correctness axiom is added. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowArithmeticBetaCertificates
open GorbowSyntax
open LogicLineages.OrdinalComparison.TerminationOrdering

def closedBeta (a b i r : Nat) : Sentence :=
  GorbowArithmeticCompositionCertificates.closedArithmetic OrdinaryArithmetic.betaGraph ![a,b,i,r]

def modulus {n : Nat} (b i : Nat) : Term n :=
  .succ (.mul (.succ (Term.numeral i)) (Term.numeral b))

/-- The exact implication/falsum conjunction encoding in the beta body. -/
def matrix {n : Nat} (a b i r : Nat) (q d : Term n) : Formula n :=
  .imp (.imp (.equal (Term.numeral a) (.add (.mul q (modulus b i)) (Term.numeral r)))
    (.imp (.equal (.add (Term.numeral r) (.succ d)) (modulus b i))
      GorbowArithmeticCompositionCertificates.falseFormula))
    GorbowArithmeticCompositionCertificates.falseFormula

/-- The inner binder is the strict-bound witness d; q is retained. -/
def quotientBody (a b i r : Nat) : Formula 1 :=
  .imp (.all (.imp (matrix a b i r (.var 1) (.var 0))
    GorbowArithmeticCompositionCertificates.falseFormula))
    GorbowArithmeticCompositionCertificates.falseFormula

def literalBeta (a b i r : Nat) : Sentence :=
  GorbowArithmeticCompositionCertificates.encodedExists (quotientBody a b i r)

/-- Retain ONLY the entry value r, without reassigning the two code components. -/
def valueBody (a b i : Nat) : Formula 1 :=
  GorbowFormulaSubstitution.substituteFormula
    (Fin.cases (Term.numeral a) (Fin.cases (Term.numeral b)
      (Fin.cases (Term.numeral i) (fun _ : Fin 1 => (.var 0 : Term 1)))))
    (GorbowOrdinaryArithmeticGraphs.translateBounded OrdinaryArithmetic.betaGraph id Fin.elim0)

end LogicLineages.ComputabilityKnowledge.GorbowArithmeticBetaCertificates
