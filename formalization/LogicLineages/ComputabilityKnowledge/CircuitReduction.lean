module

public import LogicLineages.ComputabilityKnowledge.Comparators.MultiplicationGadget
public import LogicLineages.ComputabilityKnowledge.Comparators.ExponentialGap

@[expose] public section

/-!
# Positive straight-line circuits and literal multiplication elimination

Paper02, lines 191–210. A constant parameter `k` denotes the positive number
`k+1`. Gates may reuse earlier wires, but may not reference themselves or later
wires. Inputs occupy `[0,n)`; gate i writes `n+i`; its eight reserved auxiliary
slots begin at `n+length+8*i`. The output equality is retained even for an empty
circuit. This module specifies an executable construction, not an MRDP supplier
or a certificate of recursive computability. Those are separate obligations.
-/
namespace LogicLineages.ComputabilityKnowledge.CircuitReduction

open PositiveExpression
abbrev System := List (Expr Nat × Expr Nat)

inductive Gate where
  | constant : Nat → Gate
  | add : Nat → Nat → Gate
  | mul : Nat → Nat → Gate
  deriving DecidableEq

structure Circuit where
  inputCount : Nat
  gates : List Gate
  leftOutput : Nat
  rightOutput : Nat
  deriving DecidableEq

def Gate.ValidAt (bound : Nat) : Gate → Prop
  | .constant _ => True
  | .add x y | .mul x y => x < bound ∧ y < bound

def ValidFrom : Nat → List Gate → Prop
  | _, [] => True
  | next, g :: gs => g.ValidAt next ∧ ValidFrom (next + 1) gs

def Circuit.WellFormed (c : Circuit) : Prop :=
  ValidFrom c.inputCount c.gates ∧
    c.leftOutput < c.inputCount + c.gates.length ∧
    c.rightOutput < c.inputCount + c.gates.length

def Gate.eval (ρ : Nat → PosNat) : Gate → PosNat
  | .constant k => ⟨k + 1, Nat.zero_lt_succ k⟩
  | .add x y => ⟨(ρ x).val + (ρ y).val, Nat.add_pos_left (ρ x).property _⟩
  | .mul x y => ⟨(ρ x).val * (ρ y).val, Nat.mul_pos (ρ x).property (ρ y).property⟩

def assign (ρ : Nat → PosNat) (i : Nat) (v : PosNat) : Nat → PosNat :=
  fun j => if j = i then v else ρ j

def run : Nat → List Gate → (Nat → PosNat) → (Nat → PosNat)
  | _, [], ρ => ρ
  | next, g :: gs, ρ => run (next + 1) gs (assign ρ next (g.eval ρ))

def Circuit.outputEqual (c : Circuit) (ρ : Nat → PosNat) : Prop :=
  (run c.inputCount c.gates ρ c.leftOutput).val =
    (run c.inputCount c.gates ρ c.rightOutput).val

/-- Parameter k expands to exactly k+1 copies of the source constant one. -/
def positiveNumeral : Nat → Expr Nat
  | 0 => .one
  | k + 1 => .add (positiveNumeral k) .one

def auxiliary (base gateIndex slot : Nat) : Nat := base + 8 * gateIndex + slot

def gadgetNames (x y w base gateIndex : Nat) :
    Comparators.MultiplicationGadget.Variable → Nat
  | .x => x
  | .y => y
  | .w => w
  | .s => auxiliary base gateIndex 0
  | .t => auxiliary base gateIndex 1
  | .u => auxiliary base gateIndex 2
  | .v => auxiliary base gateIndex 3
  | .q => auxiliary base gateIndex 4
  | .r => auxiliary base gateIndex 5
  | .h => auxiliary base gateIndex 6
  | .k => auxiliary base gateIndex 7

def gateEquations (wire base gateIndex : Nat) : Gate → System
  | .constant k => [(.var wire, positiveNumeral k)]
  | .add x y => [(.var wire, .add (.var x) (.var y))]
  | .mul x y => Comparators.MultiplicationGadget.equations.map
      (fun pair => (pair.1.rename (gadgetNames x y wire base gateIndex),
        pair.2.rename (gadgetNames x y wire base gateIndex)))

def compileGates (base : Nat) : Nat → Nat → List Gate → System
  | _, _, [] => []
  | next, i, g :: gs => gateEquations next base i g ++
      compileGates base (next + 1) (i + 1) gs

def compile (c : Circuit) : System :=
  compileGates (c.inputCount + c.gates.length) c.inputCount 0 c.gates ++
    [(.var c.leftOutput, .var c.rightOutput)]

def variableBound (c : Circuit) : Nat := c.inputCount + 9 * c.gates.length

def Bounded (bound : Nat) : Expr Nat → Prop
  | .one => True
  | .var i => i < bound
  | .add a b | .emul a b => Bounded bound a ∧ Bounded bound b

def ExtendsInputs (n : Nat) (ρ τ : Nat → PosNat) : Prop :=
  ∀ i, i < n → τ i = ρ i

/-- All expressions have literal prefix tags; no general product constructor. -/
def encodeExpr : Expr Nat → List Nat
  | .one => [0]
  | .var i => [1, i]
  | .add a b => 2 :: (encodeExpr a ++ encodeExpr b)
  | .emul a b => 3 :: (encodeExpr a ++ encodeExpr b)

/-- Length framing makes expression-pair and system boundaries explicit. -/
def encodeSystem : System → List Nat
  | [] => []
  | (a,b) :: rest => (encodeExpr a).length :: ((encodeExpr b).length ::
      (encodeExpr a ++ encodeExpr b ++ encodeSystem rest))

def encodeGate : Gate → List Nat
  | .constant k => [0, k, 0]
  | .add x y => [1, x, y]
  | .mul x y => [2, x, y]

def encodeGates : List Gate → List Nat
  | [] => []
  | g :: gs => encodeGate g ++ encodeGates gs

def decodeGates : List Nat → Option (List Gate)
  | [] => some []
  | 0 :: k :: 0 :: rest => (decodeGates rest).map (Gate.constant k :: ·)
  | 1 :: x :: y :: rest => (decodeGates rest).map (Gate.add x y :: ·)
  | 2 :: x :: y :: rest => (decodeGates rest).map (Gate.mul x y :: ·)
  | _ => none

def encodeCircuit (c : Circuit) : List Nat :=
  c.inputCount :: c.leftOutput :: c.rightOutput :: encodeGates c.gates

def decodeCircuit : List Nat → Option Circuit
  | n :: l :: r :: rest => (decodeGates rest).map (fun gs => ⟨n, gs, l, r⟩)
  | _ => none

/-- Malformed codes return none. Well-formedness is a separate semantic property. -/
def compileCode (code : List Nat) : Option (List Nat) :=
  (decodeCircuit code).map (fun c => encodeSystem (compile c))

end LogicLineages.ComputabilityKnowledge.CircuitReduction
