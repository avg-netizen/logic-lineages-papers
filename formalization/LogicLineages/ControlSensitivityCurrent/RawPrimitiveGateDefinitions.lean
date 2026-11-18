module
public import LogicLineages.ControlSensitivityCurrent.RawCheckedCompositionDefinitions
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGRawValidatorDefinitions
public import LogicLineages.OrdinalComparison.SourcePrimitiveLoweringDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PrimitiveGate

open LogicLineages.OrdinalComparison.Source PrimitiveLowering
open CheckedComposition (rawNode)

/-- Port zero is the constant; a nonzero port is one plus the free variable index. -/
def encodePort {Γ : List Ty} : Port Γ → Nat
  | .zero => 0
  | .var x => variableIndex x + 1

/-- Tag followed by four port slots. Unused slots must be zero. -/
abbrev GateCode := Nat × Nat × Nat × Nat × Nat

def encodeGate {Γ : List Ty} : Gate Γ → GateCode
  | .eq a b => (0, encodePort a, encodePort b, 0, 0)
  | .add a b c => (1, encodePort a, encodePort b, encodePort c, 0)
  | .sort a b l h => (2, encodePort a, encodePort b, encodePort l, encodePort h)
  | .one a => (3, encodePort a, 0, 0, 0)

def portGuard (context : List Nat) (p : Nat) : Bool :=
  if p = 0 then true else RawValidator.«variable» context 0 (p - 1)

def gateGuard (context : List Nat) (g : GateCode) : Bool :=
  let (tag, a, b, c, d) := g
  let ports := portGuard context a && portGuard context b &&
    portGuard context c && portGuard context d
  ports && (decide (tag = 0 ∧ c = 0 ∧ d = 0) || decide (tag = 1 ∧ d = 0) ||
    decide (tag = 2) || decide (tag = 3 ∧ b = 0 ∧ c = 0 ∧ d = 0))

def blockContext (context : List Nat) : List Nat := List.replicate 9 0 ++ context

def liftPortRaw (p : Nat) : Nat := if p = 0 then 0 else p + 9

def portNode (localTypes : List Nat) (p : Nat) : Node :=
  if p = 0 then (localTypes, 0, 3, []) else (localTypes, 0, 0, [p - 1])

def portRaw (context : List Nat) (p : Nat) : Code :=
  (context, [portNode [] p], 0, 0)

def successorRaw (context : List Nat) (p : Nat) : Code :=
  (context, [rawNode 0 1 [0, 0, 1], rawNode (SyntaxCode.arrowCode 0 0) 4 [], portNode [] p], 0, 0)

def eraseRaw (context : List Nat) (a b : Nat) : Code :=
  (context, [rawNode 0 1 [0, 1, 0], portNode [] b, rawNode (SyntaxCode.arrowCode 0 0) 2 [0, 0, 0],
    portNode [0] (if a = 0 then 0 else a + 1)], 0, 0)

def identityZeroRaw (context : List Nat) : Code :=
  (context, [rawNode 0 1 [0, 1, 0], portNode [] 0, rawNode (SyntaxCode.arrowCode 0 0) 2 [0, 0, 0],
    portNode [0] 1], 0, 0)

def addRaw (context : List Nat) (a b c d : Nat) : List (Code × Code) :=
  [(eraseRaw context b 0, eraseRaw context 0 d), (eraseRaw context a d, eraseRaw context c 0)]

def unusedRaw (context : List Nat) (start : Nat) : List (Code × Code) :=
  ((List.range 9).drop start).map (fun i => (portRaw context (i + 1), portRaw context 0))

/-- Literal ten-equation output of each gate in the same fresh nine-name block. -/
def forestRaw (context : List Nat) (g : GateCode) : List (Code × Code) :=
  let context := blockContext context
  let (tag, a, b, c, d) := g
  let a := liftPortRaw a
  let b := liftPortRaw b
  let c := liftPortRaw c
  let d := liftPortRaw d
  if tag = 0 then
    (portRaw context a, portRaw context b) :: unusedRaw context 0
  else if tag = 1 then
    addRaw context a b c 1 ++ unusedRaw context 1
  else if tag = 2 then
    [(successorRaw context a, portRaw context 1), (successorRaw context b, portRaw context 2),
      (successorRaw context c, portRaw context 3), (successorRaw context d, portRaw context 4)] ++
    addRaw context 1 2 5 7 ++ addRaw context 3 4 5 8 ++ addRaw context c 6 d 9
  else
    (successorRaw context 1, identityZeroRaw context) ::
      (addRaw context a a 1 2 ++ unusedRaw context 2)

def compile (context : List Nat) (g : GateCode) : Option (List (Code × Code)) :=
  if gateGuard context g then some (forestRaw context g) else none

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PrimitiveGate
