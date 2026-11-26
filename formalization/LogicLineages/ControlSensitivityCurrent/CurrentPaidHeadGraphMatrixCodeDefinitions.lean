module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphFoundationDefinitions
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionEmitterDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.MatrixCode

open LogicLineages.OrdinalComparison.Source
open RawSourceDAG (Code encode variableIndex)
open RawSourceDAG.InputCompiler (InputCode InputStep)

/-- Serialized literal SourceAST nodes; their DAG payloads and variable
indices are the existing actual encoders, not evaluator handles. -/
def var (i : Nat) : Nat := 8*i
def lit (n : Nat) : Nat := 8*n+1
def add (a b : Nat) : Nat := 8*Nat.pair a b+2
def observe (a : Code) : Nat := 8*Encodable.encode a+3
def unary (h : Code) (a : Nat) : Nat := 8*Nat.pair (Encodable.encode h) a+4

def atom (tag a b : Nat) : Nat := 8*Nat.pair a b+tag
def neg (a : Nat) : Nat := 8*a+5
def both (a b : Nat) := atom 6 a b
def either (a b : Nat) := atom 7 a b
def eq (a b : Nat) := atom 2 a b
def le (a b : Nat) := atom 3 a b
def lt (a b : Nat) := atom 4 a b

def term {Γ : List Ty} : SourceAST.Term Γ → Nat
  | .var x => var (variableIndex x)
  | .literal n => lit n
  | .add a b => add (term a) (term b)
  | .observation a => observe (encode ⟨Γ,.ground,a⟩)
  | .unary h a => unary (encode ⟨[],.arrow .ground .ground,h⟩) (term a)

def formula {Γ : List Ty} : SourceAST.Formula Γ → Nat
  | .truth => 0
  | .falsity => 1
  | .eq a b => eq (term a) (term b)
  | .le a b => le (term a) (term b)
  | .lt a b => lt (term a) (term b)
  | .neg a => neg (formula a)
  | .conj a b => both (formula a) (formula b)
  | .disj a b => either (formula a) (formula b)

def blank : Code := ([],[],0,0)
def payload (n : Nat) : Code := (Encodable.decode (α := Code) n).getD blank

def renameTerm (ctx table : List Nat) (code : Nat) : Nat :=
  let tag := code%8
  let n := code/8
  if tag=0 then var (table.getD n 0)
  else if h : tag=2 ∨ tag=4 then
    have hd : n < code := Nat.div_lt_self (by dsimp [tag] at h; omega) (by decide)
    have hl : n.unpair.1 < code := (Nat.unpair_left_le _).trans_lt hd
    have hr : n.unpair.2 < code := (Nat.unpair_right_le _).trans_lt hd
    if tag=2 then add (renameTerm ctx table n.unpair.1) (renameTerm ctx table n.unpair.2)
    else unary (payload n.unpair.1) (renameTerm ctx table n.unpair.2)
  else if tag=3 then observe (RawSourceDAG.Operations.renameCode ctx table (payload n))
  else lit n
termination_by code
decreasing_by all_goals assumption

def renameFormula (ctx table : List Nat) (code : Nat) : Nat :=
  let tag := code%8
  let n := code/8
  if h : 5 ≤ tag then
    have hd : n < code := Nat.div_lt_self (by dsimp [tag] at h; omega) (by decide)
    have hl : n.unpair.1 < code := (Nat.unpair_left_le _).trans_lt hd
    have hr : n.unpair.2 < code := (Nat.unpair_right_le _).trans_lt hd
    if tag=5 then neg (renameFormula ctx table n)
    else atom tag (renameFormula ctx table n.unpair.1) (renameFormula ctx table n.unpair.2)
  else if 2 ≤ tag then
    atom tag (renameTerm ctx table n.unpair.1) (renameTerm ctx table n.unpair.2)
  else tag
termination_by code
decreasing_by all_goals assumption

def times (d a : Nat) : Nat := Nat.rec (lit 0) (fun _ t => add a t) d
def raw (i : Nat) : Nat := add (var i) (lit 1)
def conjunction (xs : List Nat) : Nat := xs.foldr both 0
def disjunction (xs : List Nat) : Nat := xs.foldr either 1

/-- The actual InputNormalization input steps with natural-variable index
and Boolean-reference accounting in the current compiler conventions. -/
abbrev Emit := List InputStep × Nat × Nat

def liftPort (n x : Nat) : Nat := if x=0 then 0 else x+n
def noneStep (tag a b : Nat) : InputStep := ((tag,a,b),none)
def sourceStep (tag i : Nat) (d : Code) : InputStep := ((tag,i,0),some d)

/-- Return row list, number of fresh natural binders, coded resulting port.
The numeric offset is relative to the SAME original AST context. -/
def emitTerm (offset code : Nat) : Emit :=
  let tag := code%8
  let n := code/8
  if tag=0 then ([],0,n+offset+1)
  else if h : tag=2 ∨ tag=4 then
    have hd : n < code := Nat.div_lt_self (by dsimp [tag] at h; omega) (by decide)
    have hl : n.unpair.1 < code := (Nat.unpair_left_le _).trans_lt hd
    have hr : n.unpair.2 < code := (Nat.unpair_right_le _).trans_lt hd
    if tag=2 then
      let (ls,d,v) := emitTerm offset n.unpair.1
      let (rs,e,w) := emitTerm (offset+d) n.unpair.2
      (ls++rs++[noneStep 6 (liftPort e v) w],d+e+1,1)
    else
      let (rs,d,v) := emitTerm offset n.unpair.2
      (rs++[noneStep 6 v 0,sourceStep 9 0 (payload n.unpair.1)],d+2,1)
  else if tag=3 then
    ([sourceStep 8 0 (CurrentDecisionEmitter.liftCode offset (payload n))],1,1)
  else ([noneStep 7 n 0],1,1)
termination_by code
decreasing_by all_goals assumption

/-- Return row list, number of fresh natural binders, number of fresh
Boolean references. Each successful form's root is the latest row (index 0). -/
def emitFormula (offset code : Nat) : Emit :=
  let tag := code%8
  let n := code/8
  if h : 5 ≤ tag then
    have hd : n < code := Nat.div_lt_self (by dsimp [tag] at h; omega) (by decide)
    have hl : n.unpair.1 < code := (Nat.unpair_left_le _).trans_lt hd
    have hr : n.unpair.2 < code := (Nat.unpair_right_le _).trans_lt hd
    if tag=5 then
      let (ls,d,m) := emitFormula offset n
      (ls++[noneStep 3 0 0],d,m+1)
    else
      let (ls,d,m) := emitFormula offset n.unpair.1
      let (rs,e,k) := emitFormula (offset+d) n.unpair.2
      (ls++rs++[noneStep (tag-2) k 0],d+e,m+k+1)
  else if 2 ≤ tag then
    let (ls,d,v) := emitTerm offset n.unpair.1
    let (rs,e,w) := emitTerm (offset+d) n.unpair.2
    (ls++rs++[noneStep (tag-2) (liftPort e v) w],d+e,1)
  else ([noneStep (if tag=0 then 0 else 2) 0 0],0,1)
termination_by code
decreasing_by all_goals assumption

def inputCode (code : Nat) : InputCode := ((emitFormula 0 code).1,0)

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.MatrixCode
