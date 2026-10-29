module

public import LogicLineages.ComputabilityKnowledge.FiniteComparisonEnumeration

@[expose] public section

/-! Literal affine envelope from paper02 lines257–280. Depth is the existing
Expr.depth: addition takes max and E adds one to the max of both operands.
No ordinal ψ/C membership or fast-growing-hierarchy conclusion is asserted. -/
namespace LogicLineages.ComputabilityKnowledge.FiniteDepthEnvelope

open PositiveExpression CircuitReduction FiniteComparisonEnumeration

def nodeCount : Expr Nat → Nat
  | .one => 1
  | .var _ => 1
  | .add a b | .emul a b => nodeCount a + nodeCount b + 1

def rawVariables : Expr Nat → List Nat
  | .one => []
  | .var i => [i]
  | .add a b | .emul a b => rawVariables a ++ rawVariables b

def insertVariable (i : Nat) (xs : List Nat) : List Nat := if i ∈ xs then xs else i::xs

def distinctVariables (xs : List Nat) : List Nat := xs.foldr insertVariable []
def variableList (e : Expr Nat) : List Nat := distinctVariables (rawVariables e)

def variableSum (xs : List Nat) : Expr Nat := xs.foldr (fun i r => .add (.var i) r) .one

/-- `scale k e` is (k+1) literal copies, never a multiplication constructor. -/
def scale : Nat → Expr Nat → Expr Nat
  | 0,e => e
  | k+1,e => .add e (scale k e)

def s0 (e : Expr Nat) : Expr Nat := variableSum (variableList e)
def bTerm (e : Expr Nat) : Expr Nat := scale (nodeCount e) (s0 e)
def envelope (e : Expr Nat) : Expr Nat := scale 4 (bTerm e)

def tokenVariables (ts : List Token) : List Nat :=
  ts.foldr (fun t xs => if t.1 = 1 then insertVariable t.2 xs else xs) []

def encodeVariableSum (xs : List Nat) : List Nat := xs.foldr (fun i r => 2::1::i::r) [0]
def encodeScale (k : Nat) (xs : List Nat) : List Nat := Nat.rec xs (fun _ r => 2::(xs++r)) k

def tokenEnvelope (ts : List Token) : List Nat :=
  encodeScale 4 (encodeScale ts.length (encodeVariableSum (tokenVariables ts)))

/-- Existing numerical validity check rejects exactly malformed/out-of-bound
expressions; the output is the existing literal Expr prefix codec. -/
def envelopeCode (d : Nat) (xs : List Nat) : Option (List Nat) :=
  (evalCode d xs []).bind (fun _ => (tokenize xs).map tokenEnvelope)

end LogicLineages.ComputabilityKnowledge.FiniteDepthEnvelope
