module

public import LogicLineages.ComputabilityKnowledge.GorbowVariableCode
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowVariableCode
open GorbowSyntax GorbowCodeConstructors
open LogicLineages.ComputabilityKnowledge.GorbowVariableCode

def ActualCalibration : Prop := ∀ n (i : Fin n), variableNumber i.val=termNumber (Term.var i)
def Injection : Prop := Function.Injective variableNumber

def ExactDecoding : Prop := ∀ code i, decodeVariable code=some i ↔ code=variableNumber i

def ExactDomain : Prop := ∀ code, isVariableCode code=true ↔ ∃ i,code=variableNumber i

def MalformedRejection : Prop := ∀ code, decodeVariable code=none ↔ ¬ ∃ i,code=variableNumber i

def UniformPrograms : Prop := Primrec variableNumber ∧ Primrec decodeVariable ∧ Primrec isVariableCode

def Target : Prop := ActualCalibration ∧ Injection ∧ ExactDecoding ∧ ExactDomain ∧ MalformedRejection ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowVariableCode
