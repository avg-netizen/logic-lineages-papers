module

public import LogicLineages.ComputabilityKnowledge.GorbowClosedTermCode
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowClosedTermCode
open GorbowSyntax GorbowStandardInstances GorbowCodeConstructors
open LogicLineages.ComputabilityKnowledge.GorbowClosedTermCode

def ClosedTokenCalibration : Prop := ∀ t : Term 0,
  ((GorbowTermPrefixCode.encode t).all (fun tag => decide (tag≠5))=true ↔ ArithmeticTerm t)
def ExactRawArithmetic : Prop := ∀ raw, arithmeticRaw raw=true ↔
  ∃ t : Term 0, raw=GorbowTermPrefixCode.encode t ∧ ArithmeticTerm t

def ExactNumericDomains : Prop :=
  (∀ code, fullTermCode code=true ↔ ∃ t : Term 0, code=termNumber t) ∧
  (∀ code, arithmeticTermCode code=true ↔ ∃ t : Term 0, code=termNumber t ∧ ArithmeticTerm t)

def NumeralCoverage : Prop := ∀ k,
  fullTermCode (termNumber (Term.numeral (n:=0) k))=true ∧
  arithmeticTermCode (termNumber (Term.numeral (n:=0) k))=true

def Inclusion : Prop := ∀ code, arithmeticTermCode code=true → fullTermCode code=true

def UniformPrograms : Prop := Primrec arithmeticRaw ∧ Primrec fullTermCode ∧ Primrec arithmeticTermCode

def Target : Prop := ClosedTokenCalibration ∧ ExactRawArithmetic ∧ ExactNumericDomains ∧ NumeralCoverage ∧ Inclusion ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowClosedTermCode
