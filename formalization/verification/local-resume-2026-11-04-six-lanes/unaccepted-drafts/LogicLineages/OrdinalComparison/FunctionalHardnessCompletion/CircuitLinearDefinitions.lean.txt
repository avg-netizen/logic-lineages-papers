module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.UndecidabilityDefinitions
public import LogicLineages.ComputabilityKnowledge.CircuitReduction
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitLinear
open LogicLineages.ComputabilityKnowledge.CircuitReduction
abbrev Row := List MonomialCode

def constant (c : Int) (power : Nat := 0) : MonomialCode := (c,power,none)
def wireMonomial (c : Int) (power index : Nat) : MonomialCode := (c,power,some index)

/-- Literal three equations from the checked square gadget. Parameters u,v
are scalar wires; the four fresh polynomial witnesses start at aux. -/
def squareRows (u v aux : Nat) : List Row :=
  [[wireMonomial 1 1 aux,wireMonomial (-1) 0 aux,wireMonomial (-1) 0 (aux+3),constant 1],
   [wireMonomial 1 1 (aux+1),wireMonomial (-1) 0 (aux+1),wireMonomial (-1) 0 aux,wireMonomial 1 0 u],
   [wireMonomial 1 1 (aux+2),wireMonomial (-1) 0 (aux+2),wireMonomial (-1) 0 (aux+1),wireMonomial 1 0 v]]

/-- V, extra, U1,U2,U3,W1,W2,Y1,Y2 occupy nine consecutive fresh wires.
Only the original scalar block is required to be constant; the seven
geometric-polynomial witnesses remain unrestricted N[X] unknowns. -/
def constantRows (scalarCount aux : Nat) : List Row :=
  [[wireMonomial 1 1 (aux+2),wireMonomial (-1) 0 (aux+2),wireMonomial (-1) 0 (aux+5),constant 1],
   [wireMonomial 1 2 (aux+3),wireMonomial (-1) 0 (aux+3),wireMonomial (-1) 0 (aux+6),constant 1],
   [wireMonomial 1 1 (aux+4),wireMonomial (-1) 0 (aux+4),wireMonomial (-1) 0 (aux+3),wireMonomial 1 0 (aux+2)],
   [wireMonomial 1 1 (aux+7),wireMonomial (-2) 0 (aux+7),wireMonomial (-1) 0 (aux+2),wireMonomial 1 0 aux],
   [wireMonomial 1 2 (aux+8),wireMonomial (-2) 0 (aux+8),wireMonomial (-1) 0 (aux+3),wireMonomial 1 0 aux],
   (List.range scalarCount).map (wireMonomial 1 0) ++ [wireMonomial 1 0 (aux+1),wireMonomial (-1) 0 aux]]

def scalarCount (n g : Nat) : Nat := (n+g)+n+4*g
def polynomialAux (n g : Nat) : Nat := scalarCount n g
def constantAux (n g : Nat) : Nat := scalarCount n g+12*g
def unknownCount (n g : Nat) : Nat := constantAux n g+9

/-- Reserving four scalar and twelve polynomial slots at EVERY gate makes
allocation independent of gate tags. Unused scalar slots can be zero, and
unused polynomial slots are unconstrained. No original wire is duplicated. -/
def gateRows (n g i : Nat) : Gate → List Row
  | .constant k => [[wireMonomial 1 0 (n+i),constant (-((k+1 : Nat) : Int))]]
  | .add x y => [[wireMonomial 1 0 (n+i),wireMonomial (-1) 0 x,wireMonomial (-1) 0 y]]
  | .mul x y =>
      let s := (n+g)+n+4*i
      let a := polynomialAux n g+12*i
      [[wireMonomial 1 0 s,wireMonomial (-1) 0 x,wireMonomial (-1) 0 y],
       [wireMonomial 1 0 (s+3),wireMonomial (-1) 0 (s+1),wireMonomial (-1) 0 (s+2),wireMonomial (-1) 0 (n+i)]] ++
      squareRows x (s+1) a ++ squareRows y (s+2) (a+4) ++ squareRows s (s+3) (a+8)

/-- Each positive circuit input y receives one scalar slack x with y=x+1.
This retains zero-valued roots of the original polynomial after the already
checked nonnegative-to-positive polynomial shift. -/
def inputRows (n g : Nat) : List Row :=
  (List.range n).map fun i =>
    [wireMonomial 1 0 i,wireMonomial (-1) 0 (n+g+i),constant (-1)]

def encodeCircuitSystem (c : Circuit) : SystemCode :=
  let n := c.inputCount
  let g := c.gates.length
  (unknownCount n g,
   inputRows n g ++
   (c.gates.zipIdx.flatMap fun gi => gateRows n g gi.2 gi.1) ++
   [[wireMonomial 1 0 c.leftOutput,wireMonomial (-1) 0 c.rightOutput]] ++
   constantRows (scalarCount n g) (constantAux n g))

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitLinear
