module

public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProductCode
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalizer
public import LogicLineages.ComputabilityKnowledge.FiniteComparisonEnumeration

@[expose] public section

/-! Literal prefix-code normalizer. The lexer is the existing source lexer.
The stack is processed from the right, exactly as in the existing prefix
decoder. A row stores the finite vector of output codes at heights0..H, so
an E-node at height h+1 can read its operands' height-h entries. A separate
numeric stack computes the original expression depth before selecting H.
No AST computability instance, semantic-map oracle, or normalization theorem
is used in these executable definitions.
-/
namespace LogicLineages.ComputabilityKnowledge.ExponentialNormalizerProgram

open PositiveExpression ExponentialHereditaryCodec
open ExponentialNormalFormCodeOperations ExponentialNormalFormProductCode
open FiniteComparisonEnumeration

def processStep {α : Type} (one : α) (variableValue : Nat → α)
    (addition exponential : α → α → α) (d : Nat) (t : Token)
    (stack : List α) : Option (List α) :=
  match t.1 with
  | 0 => some (one :: stack)
  | 1 => if t.2 < d then some (variableValue t.2 :: stack) else none
  | 2 => match stack with
      | a :: b :: rest => some (addition a b :: rest)
      | _ => none
  | 3 => match stack with
      | a :: b :: rest => some (exponential a b :: rest)
      | _ => none
  | _ => none

def processStack {α : Type} (one : α) (variableValue : Nat → α)
    (addition exponential : α → α → α) (d : Nat) (ts : List Token) : Option (List α) :=
  ts.foldr (fun t result => result.bind (processStep one variableValue addition exponential d t))
    (some [])

def processCode {α : Type} (one : α) (variableValue : Nat → α)
    (addition exponential : α → α → α) (d : Nat) (raw : List Nat) : Option α := do
  let ts ← tokenize raw
  let stack ← processStack one variableValue addition exponential d ts
  match stack with
  | [value] => some value
  | _ => none

def oneRow (d H : Nat) : List Nat :=
  (List.range (H + 1)).map (fun h => constantCode d h 1)

def variableRow (d H i : Nat) : List Nat :=
  (List.range (H + 1)).map (fun h => variableCode d h i)

def additionRow (d H : Nat) (a b : List Nat) : List Nat :=
  (List.range (H + 1)).map (fun h => addCode d h (a.getD h 0) (b.getD h 0))

def exponentialRow (d H : Nat) (a b : List Nat) : List Nat :=
  (List.range (H + 1)).map (fun h =>
    match h with
    | 0 => zeroCode d 0
    | k + 1 => exponentialProductCode d k (a.getD k 0) (b.getD k 0))

def expressionRow (d H : Nat) : Expr (Fin d) → List Nat
  | .one => oneRow d H
  | .var i => variableRow d H i.val
  | .add a b => additionRow d H (expressionRow d H a) (expressionRow d H b)
  | .emul a b => exponentialRow d H (expressionRow d H a) (expressionRow d H b)

def compileAt (d H : Nat) (raw : List Nat) : Option Nat :=
  (processCode (oneRow d H) (variableRow d H) (additionRow d H)
    (exponentialRow d H) d raw).map (fun row => row.getD H 0)

def depthCode (d : Nat) (raw : List Nat) : Option Nat :=
  processCode 0 (fun _ => 0) Nat.max (fun a b => max a b + 1) d raw

def normalizeCode (d : Nat) (raw : List Nat) : Option (Nat × Nat) := do
  let h ← depthCode d raw
  let n ← compileAt d h raw
  pure (h, n)

end LogicLineages.ComputabilityKnowledge.ExponentialNormalizerProgram
