module
public import LogicLineages.ControlSensitivityCurrent.RawBooleanMatrixDefinitions
public import LogicLineages.ControlSensitivityCurrent.InputNormalizationDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler

open LogicLineages.OrdinalComparison.Source
open BinaryPlanCompiler (binder gate shiftPort prefixTable constantRaw)
open PrimitiveGate (encodePort portGuard portRaw)
open BooleanMatrix (RowCode addCode matrixRaw)
open PlanCompiler (Instruction)

abbrev InputStep := RowCode × Option Code
abbrev InputCode := List InputStep × Nat
abbrev Lowering := List Instruction × List Nat × Option Nat
abbrev InputState := List Nat × List RowCode × List Nat × List Lowering

def encodeInputRow {Γ : List Ty} {m : Nat} : InputNormalization.Node Γ m → RowCode
  | .eq a b => (0,encodePort a,encodePort b)
  | .le a b => (1,encodePort a,encodePort b)
  | .lt a b => (2,encodePort a,encodePort b)
  | .neg a => (3,a.val,0)
  | .conj a b => (4,a.val,b.val)
  | .disj a b => (5,a.val,b.val)

def prependStep (step : InputStep) (code : InputCode) : InputCode := (step :: code.1, code.2)

def encodeInput {Γ : List Ty} {m : Nat} : InputNormalization.Input Γ m → InputCode
  | .finish root => ([],root.val)
  | .boolean n q => prependStep (encodeInputRow n,none) (encodeInput q)
  | .add a b q => prependStep ((6,encodePort a,encodePort b),none) (encodeInput q)
  | .literal k q => prependStep ((7,k,0),none) (encodeInput q)
  | .observation d q => prependStep ((8,0,0),some (encode ⟨Γ,.ground,d⟩)) (encodeInput q)
  | .unary h x q => prependStep ((9,variableIndex x,0),some (encode ⟨[],.arrow .ground .ground,h⟩))
      (encodeInput q)

def booleanGuard (context : List Nat) (m : Nat) (row : RowCode) : Bool :=
  let (tag,a,b) := row
  if tag < 3 then portGuard context a && portGuard context b
  else if tag = 3 then decide (a < m ∧ b = 0)
  else decide ((tag = 4 ∨ tag = 5) ∧ a < m ∧ b < m)

def addRow (s : InputState) (row : RowCode) : InputState :=
  let (context,rows,ports,pending) := s
  let (tag,a,b) := row
  if tag < 3 then
    (context,(tag,ports.length,ports.length+1)::rows,ports++[a,b],pending)
  else
    (context,row::rows,ports++[0,0],pending)

def addWire (s : InputState) (lowering : Lowering) : InputState :=
  (0::s.1,s.2.1,s.2.2.1.map (shiftPort 1),lowering::s.2.2.2)

def equationChunk (context : List Nat) (d : Code) : List Instruction :=
  let target := 0 :: context
  let lifted := Operations.renameCode target (prefixTable 1 context) d
  [binder,.inl (lifted,portRaw target 1)]

def unaryCallRaw (context : List Nat) (h : Code) (x : Nat) : Code :=
  CheckedComposition.applicationRaw 0 (Operations.renameCode context [] h) (portRaw context (x+1))

def inputDAGGuard (context : List Nat) (t : Nat) (d : Code) : Bool :=
  valid d && decide (d.1 = context ∧ d.2.2.2 = t)

def advance (s : InputState) (i : InputStep) : Option InputState :=
  let (row,payload) := i
  let (tag,a,b) := row
  let context := s.1
  match payload with
  | none =>
    if tag < 6 then
      if booleanGuard context s.2.1.length row then some (addRow s row) else none
    else if tag = 6 ∧ portGuard context a ∧ portGuard context b then
      some (addWire s ([binder,gate (addCode (shiftPort 1 a) (shiftPort 1 b) 1)],[],none))
    else if tag = 7 ∧ b = 0 then
      some (addWire s ([],context,some a))
    else none
  | some d =>
    if tag = 8 ∧ a = 0 ∧ b = 0 ∧ inputDAGGuard context 0 d then
      some (addWire s (equationChunk context d,[],none))
    else if tag = 9 ∧ b = 0 ∧ inputDAGGuard [] (SyntaxCode.arrowCode 0 0) d ∧
        RawValidator.«variable» context 0 a then
      some (addWire s (equationChunk context (unaryCallRaw context d a),[],none))
    else none

def lower (tail : List Instruction) (i : Lowering) : List Instruction :=
  match i.2.2 with
  | none => i.1 ++ tail
  | some k => constantRaw i.2.1 k tail

def finishInput (s : InputState) (root : Nat) : Option (List Instruction) :=
  if root < s.2.1.length then
    some (s.2.2.2.foldl lower (matrixRaw s.2.2.1 s.2.1 root))
  else none

def runFrom (s : InputState) (code : InputCode) : Option (List Instruction) :=
  (code.1.foldl (fun state step => state.bind (fun s => advance s step)) (some s)).bind
    (fun state => finishInput state code.2)

def run (context : List Nat) (code : InputCode) : Option (List Instruction) :=
  runFrom (context,[],[],[]) code

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler
