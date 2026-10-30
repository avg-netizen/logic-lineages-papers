module

public import LogicLineages.ComputabilityKnowledge.GorbowSupportCode
public import LogicLineages.ComputabilityKnowledge.GorbowCodeConstructors

@[expose] public section

/-! Literal source E_A, N_A and theta_A code constructors. These do not define
CK_A or assert a diagonal equivalence or DCB theorem. Selectors use the existing
precisely-one-free predicate; the argument sentence is genuinely closed. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowSelectedCode
open GorbowSyntax GorbowCodeConstructors

def everyoneSentence (A : Selector) (σ : Sentence) : Sentence := everyone A (formulaNumber σ)
def theta (A : Selector) : Sentence := .imp (everyoneSentence A falseEquality) falseEquality

def everyoneRaw (a s : List Nat) : List Nat :=
  unary 10 (binary 7 (unary 2 (variableCode 0))
    (binary 7 a (binary 4 (variableCode 0) (numeral (number s)))))

def everyoneCode (a s : List Nat) : Option (List Nat) :=
  if GorbowSupportCode.selectorCode a && GorbowSyntaxValidation.validFormula 0 s then some (everyoneRaw a s) else none

def nonemptyCode (a : List Nat) : Option (List Nat) :=
  if GorbowSupportCode.selectorCode a then some (unary 11 (binary 8 (unary 2 (variableCode 0)) a)) else none

def thetaCode (a : List Nat) : Option (List Nat) := do
  let e ← everyoneCode a (GorbowFormulaPrefixCode.encode falseEquality)
  pure (binary 7 e (GorbowFormulaPrefixCode.encode falseEquality))
end LogicLineages.ComputabilityKnowledge.GorbowSelectedCode
