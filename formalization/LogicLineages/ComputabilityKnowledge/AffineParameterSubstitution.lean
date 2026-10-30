module

public import LogicLineages.ComputabilityKnowledge.ExponentialNormalizerProgram

@[expose] public section

/-! Literal affine one-parameter substitution from paper02 cor:consumers.
Zero summands are omitted; every actual coordinate requires a+b>0. A zero
pair has an explicit harmless fallback syntax but is rejected by the uniform
compiler's coefficient-domain guard. No zero/multiplication source constructor
is introduced. This is not the separate WW vector/admissibility/norm bridge. -/
namespace LogicLineages.ComputabilityKnowledge.AffineParameterSubstitution

open PositiveExpression CircuitReduction ExponentialNormalizerProgram

def copies {ι : Type} : Nat → Expr ι → Expr ι
  | 0, e => e
  | k + 1, e => .add e (copies k e)

def coordinateExpr (a b : Nat) : Expr (Fin 1) :=
  if a = 0 then copies (b - 1) .one
  else if b = 0 then copies (a - 1) (.var 0)
  else .add (copies (a - 1) (.var 0)) (copies (b - 1) .one)

def substitute {d : Nat} (as bs : List Nat) : Expr (Fin d) → Expr (Fin 1)
  | .one => .one
  | .var i => coordinateExpr (as.getD i.val 0) (bs.getD i.val 0)
  | .add a b => .add (substitute as bs a) (substitute as bs b)
  | .emul a b => .emul (substitute as bs a) (substitute as bs b)

def Admissible (d : Nat) (as bs : List Nat) : Prop :=
  as.length = d ∧ bs.length = d ∧ ∀ i : Fin d, 0 < as.getD i.val 0 + bs.getD i.val 0

def coefficientsOK (d : Nat) (as bs : List Nat) : Bool :=
  if as.length = d then if bs.length = d then
    (List.range d).foldr (fun i acc =>
      if 0 < as.getD i 0 + bs.getD i 0 then acc else false) true
    else false else false

def copiesCode : Nat → List Nat → List Nat
  | 0, raw => raw
  | k + 1, raw => 2 :: (raw ++ copiesCode k raw)

def coordinateCode (a b : Nat) : List Nat :=
  if a = 0 then copiesCode (b - 1) [0]
  else if b = 0 then copiesCode (a - 1) [1, 0]
  else 2 :: (copiesCode (a - 1) [1, 0] ++ copiesCode (b - 1) [0])

def compileCode (d : Nat) (as bs raw : List Nat) : Option (List Nat) :=
  if coefficientsOK d as bs then
    processCode [0] (fun i => coordinateCode (as.getD i 0) (bs.getD i 0))
      (fun a b => 2 :: (a ++ b)) (fun a b => 3 :: (a ++ b)) d raw
  else none

end LogicLineages.ComputabilityKnowledge.AffineParameterSubstitution
