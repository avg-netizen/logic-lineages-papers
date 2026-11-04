module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumericPrecedenceCertificateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticTypedCarrierProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticPrecedence
open OrdinaryArithmetic NumericPrecedenceCertificate
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def rankValue (n : Nat) (v : List.Vector Nat 2) : Nat :=
  (numericRankTest n (v.get 0) (v.get 1)).toNat

def rankGraph (p : Program 2) : Formula (Fin 2) :=
  applyGraph (graphFormula p) (succTerm zeroTerm) ![.var 0,.var 1]

def validContextGraph (p : Program 2) : Formula (Fin 1) :=
  existsFin (applyGraph (graphFormula p) (succTerm zeroTerm)
    ![.var (.inl 0),.var (.inr (0 : Fin 1))])
end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticPrecedence
