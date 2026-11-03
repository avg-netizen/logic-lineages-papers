module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCompilerTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.GuardCodeRuntime
open CommonHeadCompiler CommonHeadLargeGuards

def boolValue (ν:Nat→Nat):Formula→Bool
  | .truth=>true | .falsity=>false
  | .eq i j=>decide (ν i=ν j) | .lt i j=>decide (ν i<ν j) | .bound c i=>decide (c≤ν i)
  | .neg p=> !(boolValue ν p)
  | .conj p q=>boolValue ν p && boolValue ν q
  | .disj p q=>boolValue ν p || boolValue ν q

/-- Literal BASE-language postfix interpreter. Comparison operands are the
same original-index valuation; no head evaluator is a runtime opcode. -/
def step (ν:Nat→Nat) (a:Instruction) (stack:List Bool):List Bool:=
  if a.1=0 then false::stack
  else if a.1=1 then true::stack
  else if a.1=2 then decide (ν a.2.1=ν a.2.2)::stack
  else if a.1=3 then decide (ν a.2.1<ν a.2.2)::stack
  else if a.1=4 then decide (a.2.1≤ν a.2.2)::stack
  else if a.1=5 then (!stack.headD false)::stack.tail
  else if a.1=6 then (stack.tail.headD false && stack.headD false)::stack.tail.tail
  else if a.1=7 then (stack.tail.headD false || stack.headD false)::stack.tail.tail
  else false::stack

def run (ν:Nat→Nat) (code:List Instruction) (stack:List Bool):List Bool:=
  code.foldl (fun s a=>step ν a s) stack

def evaluate (ν:Nat→Nat) (code:List Instruction):Bool:=(run ν code []).headD false

def codeVariables (code:List Instruction):List Nat:=code.flatMap (fun a=>
  if a.1=2∨a.1=3 then [a.2.1,a.2.2] else if a.1=4 then [a.2.2] else [])
end LogicLineages.OrdinalComparison.LayeredComparison.GuardCodeRuntime
