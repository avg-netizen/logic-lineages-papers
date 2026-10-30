module

public import LogicLineages.ComputabilityKnowledge.GorbowLogicalAxiomCode

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowArithmeticAxiomCode
open GorbowSyntax GorbowPACore GorbowCodeConstructors GorbowInstanceCode
open GorbowLogicalAxiomCode (Annotation arg guardTerms)

def encode {n : Nat} : ArithmeticInstance n → Annotation
  | .succNotZero t => (0,[GorbowTermPrefixCode.encode t])
  | .succInjective t u => (1,[GorbowTermPrefixCode.encode t,GorbowTermPrefixCode.encode u])
  | .addZero t => (2,[GorbowTermPrefixCode.encode t])
  | .addSucc t u => (3,[GorbowTermPrefixCode.encode t,GorbowTermPrefixCode.encode u])
  | .mulZero t => (4,[GorbowTermPrefixCode.encode t])
  | .mulSucc t u => (5,[GorbowTermPrefixCode.encode t,GorbowTermPrefixCode.encode u])
  | .induction φ => (6,[GorbowFormulaPrefixCode.encode φ])

def case0 (n : Nat) (args : List (List Nat)) : Option (List Nat) :=
  if guardTerms n 1 args then some (unary 6 (binary 0 (unary 2 (arg args 0)) [1])) else none

def case1 (n : Nat) (args : List (List Nat)) : Option (List Nat) :=
  if guardTerms n 2 args then some (binary 7 (binary 0 (unary 2 (arg args 0)) (unary 2 (arg args 1)))
    (binary 0 (arg args 0) (arg args 1))) else none

def case2 (n : Nat) (args : List (List Nat)) : Option (List Nat) :=
  if guardTerms n 1 args then some (binary 0 (binary 3 (arg args 0) [1]) (arg args 0)) else none

def case3 (n : Nat) (args : List (List Nat)) : Option (List Nat) :=
  if guardTerms n 2 args then some (binary 0 (binary 3 (arg args 0) (unary 2 (arg args 1)))
    (unary 2 (binary 3 (arg args 0) (arg args 1)))) else none

def case4 (n : Nat) (args : List (List Nat)) : Option (List Nat) :=
  if guardTerms n 1 args then some (binary 0 (binary 4 (arg args 0) [1]) [1]) else none

def case5 (n : Nat) (args : List (List Nat)) : Option (List Nat) :=
  if guardTerms n 2 args then some (binary 0 (binary 4 (arg args 0) (unary 2 (arg args 1)))
    (binary 3 (binary 4 (arg args 0) (arg args 1)) (arg args 0))) else none

def case6 (n : Nat) (args : List (List Nat)) : Option (List Nat) :=
  if args.length = 1 then inductionCode n (arg args 0) else none

def compile (n : Nat) (annotation : Annotation) : Option (List Nat) :=
  if annotation.1 = 0 then case0 n annotation.2
  else if annotation.1 = 1 then case1 n annotation.2
  else if annotation.1 = 2 then case2 n annotation.2
  else if annotation.1 = 3 then case3 n annotation.2
  else if annotation.1 = 4 then case4 n annotation.2
  else if annotation.1 = 5 then case5 n annotation.2
  else if annotation.1 = 6 then case6 n annotation.2
  else none
end LogicLineages.ComputabilityKnowledge.GorbowArithmeticAxiomCode
