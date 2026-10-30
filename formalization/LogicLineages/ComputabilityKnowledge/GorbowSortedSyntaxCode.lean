module

public import LogicLineages.ComputabilityKnowledge.GorbowVariableCode

@[expose] public section

/-! A sorted source-code convention built on unchanged legacy codecs.
Formulas are even, terms odd; variables are the variable subset of term codes.
Raw decoding alone asserts no AST wellformedness. No full-language semantic
transport from the legacy quote convention is postulated. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowSortedSyntaxCode
open GorbowSyntax

def tagFormula (code : Nat) : Nat := 2*code
def tagTerm (code : Nat) : Nat := 2*code+1
def formulaRawNumber (raw : List Nat) : Nat := tagFormula (GorbowCodeConstructors.number raw)
def termRawNumber (raw : List Nat) : Nat := tagTerm (GorbowCodeConstructors.number raw)
def formulaCode {n : Nat} (φ : Formula n) : Nat := tagFormula (GorbowCodeConstructors.formulaNumber φ)
def termCode {n : Nat} (t : Term n) : Nat := tagTerm (GorbowCodeConstructors.termNumber t)
def variableNumber (i : Nat) : Nat := tagTerm (GorbowVariableCode.variableNumber i)

def decodeFormulaRaw (code : Nat) : Option (List Nat) :=
  if code%2=0 then GorbowNumericCertificate.decodeFormula (code/2) else none
def decodeTermRaw (code : Nat) : Option (List Nat) :=
  if code%2=1 then GorbowNumericCertificate.decodeFormula (code/2) else none
def decodeVariable (code : Nat) : Option Nat :=
  if code%2=1 then GorbowVariableCode.decodeVariable (code/2) else none
def isVariableCode (code : Nat) : Bool := (decodeVariable code).isSome

def formulaQuote {n : Nat} (k : Nat) (φ : Formula n) : Term k := Term.numeral (formulaCode φ)
def termQuote {n : Nat} (k : Nat) (t : Term n) : Term k := Term.numeral (termCode t)
end LogicLineages.ComputabilityKnowledge.GorbowSortedSyntaxCode
