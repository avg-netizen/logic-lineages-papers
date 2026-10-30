module

public import LogicLineages.ComputabilityKnowledge.GorbowInstanceCode

@[expose] public section

/-! Literal annotations and a guarded compiler for precisely the sixteen
logical/equality schemes of the explicit PA core. This is not an opaque
logical-axiom oracle or a source definitional U/u apparatus. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowLogicalAxiomCode
open GorbowSyntax GorbowPACore GorbowCodeConstructors GorbowSyntaxValidation GorbowInstanceCode
abbrev Annotation := Nat × List (List Nat)

def arg (args : List (List Nat)) (i : Nat) : List Nat := args.getD i []
def guardFormulas (n count : Nat) (args : List (List Nat)) : Bool :=
  decide (args.length = count) && args.all (fun raw => validFormula n raw)
def guardTerms (n count : Nat) (args : List (List Nat)) : Bool :=
  decide (args.length = count) && args.all (fun raw => validTerm n raw)

def encode {n : Nat} : LogicalInstance n → Annotation
  | .k a b => (0,[GorbowFormulaPrefixCode.encode a,GorbowFormulaPrefixCode.encode b])
  | .s a b c => (1,[GorbowFormulaPrefixCode.encode a,GorbowFormulaPrefixCode.encode b,GorbowFormulaPrefixCode.encode c])
  | .classicalContraposition a b => (2,[GorbowFormulaPrefixCode.encode a,GorbowFormulaPrefixCode.encode b])
  | .andLeft a b => (3,[GorbowFormulaPrefixCode.encode a,GorbowFormulaPrefixCode.encode b])
  | .andRight a b => (4,[GorbowFormulaPrefixCode.encode a,GorbowFormulaPrefixCode.encode b])
  | .andIntro a b => (5,[GorbowFormulaPrefixCode.encode a,GorbowFormulaPrefixCode.encode b])
  | .orLeft a b => (6,[GorbowFormulaPrefixCode.encode a,GorbowFormulaPrefixCode.encode b])
  | .orRight a b => (7,[GorbowFormulaPrefixCode.encode a,GorbowFormulaPrefixCode.encode b])
  | .orElim a b c => (8,[GorbowFormulaPrefixCode.encode a,GorbowFormulaPrefixCode.encode b,GorbowFormulaPrefixCode.encode c])
  | .existsDualForward a => (9,[GorbowFormulaPrefixCode.encode a])
  | .existsDualBackward a => (10,[GorbowFormulaPrefixCode.encode a])
  | .reflexive t => (11,[GorbowTermPrefixCode.encode t])
  | .equalityReplace a t u => (12,[GorbowFormulaPrefixCode.encode a,GorbowTermPrefixCode.encode t,GorbowTermPrefixCode.encode u])
  | .allInstantiate a t => (13,[GorbowFormulaPrefixCode.encode a,GorbowTermPrefixCode.encode t])
  | .allDistribute a b => (14,[GorbowFormulaPrefixCode.encode a,GorbowFormulaPrefixCode.encode b])
  | .allVacuous a => (15,[GorbowFormulaPrefixCode.encode a])

def case0 (n : Nat) (args : List (List Nat)) : Option (List Nat) :=
  if guardFormulas n 2 args then some (binary 7 (arg args 0) (binary 7 (arg args 1) (arg args 0))) else none

def case1 (n : Nat) (args : List (List Nat)) : Option (List Nat) :=
  if guardFormulas n 3 args then some (binary 7 (binary 7 (arg args 0) (binary 7 (arg args 1) (arg args 2))) (binary 7 (binary 7 (arg args 0) (arg args 1)) (binary 7 (arg args 0) (arg args 2)))) else none

def case2 (n : Nat) (args : List (List Nat)) : Option (List Nat) :=
  if guardFormulas n 2 args then some (binary 7 (binary 7 (unary 6 (arg args 0)) (unary 6 (arg args 1))) (binary 7 (arg args 1) (arg args 0))) else none

def case3 (n : Nat) (args : List (List Nat)) : Option (List Nat) :=
  if guardFormulas n 2 args then some (binary 7 (binary 8 (arg args 0) (arg args 1)) (arg args 0)) else none

def case4 (n : Nat) (args : List (List Nat)) : Option (List Nat) :=
  if guardFormulas n 2 args then some (binary 7 (binary 8 (arg args 0) (arg args 1)) (arg args 1)) else none

def case5 (n : Nat) (args : List (List Nat)) : Option (List Nat) :=
  if guardFormulas n 2 args then some (binary 7 (arg args 0) (binary 7 (arg args 1) (binary 8 (arg args 0) (arg args 1)))) else none

def case6 (n : Nat) (args : List (List Nat)) : Option (List Nat) :=
  if guardFormulas n 2 args then some (binary 7 (arg args 0) (binary 9 (arg args 0) (arg args 1))) else none

def case7 (n : Nat) (args : List (List Nat)) : Option (List Nat) :=
  if guardFormulas n 2 args then some (binary 7 (arg args 1) (binary 9 (arg args 0) (arg args 1))) else none

def case8 (n : Nat) (args : List (List Nat)) : Option (List Nat) :=
  if guardFormulas n 3 args then some (binary 7 (binary 7 (arg args 0) (arg args 2)) (binary 7 (binary 7 (arg args 1) (arg args 2)) (binary 7 (binary 9 (arg args 0) (arg args 1)) (arg args 2)))) else none

def case9 (n : Nat) (args : List (List Nat)) : Option (List Nat) :=
  if guardFormulas (n+1) 1 args then some (binary 7 (unary 11 (arg args 0)) (unary 6 (unary 10 (unary 6 (arg args 0))))) else none

def case10 (n : Nat) (args : List (List Nat)) : Option (List Nat) :=
  if guardFormulas (n+1) 1 args then some (binary 7 (unary 6 (unary 10 (unary 6 (arg args 0)))) (unary 11 (arg args 0))) else none

def case11 (n : Nat) (args : List (List Nat)) : Option (List Nat) :=
  if guardTerms n 1 args then some (binary 0 (arg args 0) (arg args 0)) else none

def case12 (n : Nat) (args : List (List Nat)) : Option (List Nat) :=
  if args.length = 3 then do
    let left ← instanceCode n (arg args 0) (arg args 1)
    let right ← instanceCode n (arg args 0) (arg args 2)
    some (binary 7 (binary 0 (arg args 1) (arg args 2)) (binary 7 left right))
  else none

def case13 (n : Nat) (args : List (List Nat)) : Option (List Nat) :=
  if args.length = 2 then do
    let inst ← instanceCode n (arg args 0) (arg args 1)
    some (binary 7 (unary 10 (arg args 0)) inst)
  else none

def case14 (n : Nat) (args : List (List Nat)) : Option (List Nat) :=
  if guardFormulas (n+1) 2 args then some (binary 7 (unary 10 (binary 7 (arg args 0) (arg args 1))) (binary 7 (unary 10 (arg args 0)) (unary 10 (arg args 1)))) else none

def case15 (n : Nat) (args : List (List Nat)) : Option (List Nat) :=
  if args.length = 1 then do
    let shifted ← weakeningCode n (arg args 0)
    some (binary 7 (arg args 0) (unary 10 shifted))
  else none

def compile (n : Nat) (annotation : Annotation) : Option (List Nat) :=
  if annotation.1 = 0 then case0 n annotation.2
  else if annotation.1 = 1 then case1 n annotation.2
  else if annotation.1 = 2 then case2 n annotation.2
  else if annotation.1 = 3 then case3 n annotation.2
  else if annotation.1 = 4 then case4 n annotation.2
  else if annotation.1 = 5 then case5 n annotation.2
  else if annotation.1 = 6 then case6 n annotation.2
  else if annotation.1 = 7 then case7 n annotation.2
  else if annotation.1 = 8 then case8 n annotation.2
  else if annotation.1 = 9 then case9 n annotation.2
  else if annotation.1 = 10 then case10 n annotation.2
  else if annotation.1 = 11 then case11 n annotation.2
  else if annotation.1 = 12 then case12 n annotation.2
  else if annotation.1 = 13 then case13 n annotation.2
  else if annotation.1 = 14 then case14 n annotation.2
  else if annotation.1 = 15 then case15 n annotation.2
  else none
end LogicLineages.ComputabilityKnowledge.GorbowLogicalAxiomCode
