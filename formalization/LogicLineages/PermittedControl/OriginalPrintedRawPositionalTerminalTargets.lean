module
public import LogicLineages.PermittedControl.OriginalPlainTerminalMatrixTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawPositionalTerminal
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPlainTerminalMatrix (readBits)

abbrev Tape := List Nat
abbrev Stack := List Bool
abbrev State := Stack × List Bool
abbrev Args := Nat × List Bool

/-- Every atom occurrence contributes opcode 2 in its original position.
The raw payload is deliberately irrelevant to this postorder traversal;
it is the corresponding original row, not a Boolean constant. -/
def tape (code : Nat) : Tape :=
  if code % 6 ≤ 2 then [code % 6]
  else if code % 6 = 3 then tape (code / 6) ++ [3]
  else tape (code / 6).unpair.1 ++ tape (code / 6).unpair.2 ++ [code % 6]
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 6 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 6)
    have hr := Nat.unpair_right_le (code / 6)
    omega

def typedTape : NormalForm.Formula → Tape
  | .truth => [0]
  | .falsity => [1]
  | .atom _ => [2]
  | .negative p => typedTape p ++ [3]
  | .conjunction p q => typedTape p ++ typedTape q ++ [4]
  | .disjunction p q => typedTape p ++ typedTape q ++ [5]

/-- Partial machine. Each binary opcode is reached only after running
both arms of its postorder tape. A short bit bank or stack is not false. -/
def localStep (p : Nat × State) : Option State :=
  let tag := p.1
  let s := p.2.1
  let bits := p.2.2
  if tag = 0 then some (true :: s,bits)
  else if tag = 1 then some (false :: s,bits)
  else if tag = 2 then
    if 0 < bits.length then some (bits.getD 0 false :: s,bits.tail) else none
  else if tag = 3 then
    if 0 < s.length then some ((!s.getD 0 false) :: s.tail,bits) else none
  else if tag = 4 then
    if 2 ≤ s.length then some ((s.getD 1 false && s.getD 0 false) :: s.tail.tail,bits) else none
  else if tag = 5 then
    if 2 ≤ s.length then some ((s.getD 1 false || s.getD 0 false) :: s.tail.tail,bits) else none
  else none

def step (s : Option State) (tag : Nat) : Option State :=
  s.bind (fun st => localStep (tag,st))

def run (instructions : Tape) (s : Option State) : Option State := instructions.foldl step s

def extract (s : State) : Option (Bool × List Bool) :=
  if s.1.length = 1 then some (s.1.getD 0 false,s.2) else none

def readCode (p : Args) : Option (Bool × List Bool) :=
  (run (tape p.1) (some ([],p.2))).bind extract

def complete (p : Bool × List Bool) : Option Bool :=
  if p.2.length = 0 then some p.1 else none

def finishCode (p : Args) : Option Bool := (readCode p).bind complete

def ExactOriginalPositionalTape : Prop :=
  (∀ p : NormalForm.Formula, tape p.encode = typedTape p) ∧
  ∀ p : NormalForm.Formula, (typedTape p).count 2 = (LinearRows.atoms p).length

def ExactOriginalRawPositionalRead : Prop :=
  ∀ (p : NormalForm.Formula) (bits : List Bool), readCode (p.encode,bits) = readBits p bits

def ExactOriginalRawPositionalFinish : Prop :=
  ∀ (p : NormalForm.Formula) (bits : List Bool) (positive : Bool),
    finishCode (p.encode,bits) = some positive ↔ readBits p bits = some (positive,[])

def ExactOriginalRawPositionalEffectivity : Prop :=
  Primrec tape ∧ Primrec readCode ∧ Primrec finishCode

def FullOriginalPrintedRawPositionalTerminal : Prop :=
  ExactOriginalPositionalTape ∧ ExactOriginalRawPositionalRead ∧
    ExactOriginalRawPositionalFinish ∧ ExactOriginalRawPositionalEffectivity

end LogicLineages.PermittedControl.OriginalPrintedRawPositionalTerminal
