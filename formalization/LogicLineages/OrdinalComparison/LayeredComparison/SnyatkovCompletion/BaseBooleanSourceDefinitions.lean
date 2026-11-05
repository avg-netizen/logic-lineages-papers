module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceParameterDecisionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSource

/-- Literal bridge from the existing compiler's Boolean BASE output. Truth and
falsity use constant atoms; disjunction uses its exact De Morgan encoding. -/
def translate : BaseFormula.Formula → SourceFormula
  | .truth => .equal (.numeral 0) (.numeral 0)
  | .falsity => .less (.numeral 0) (.numeral 0)
  | .equal a b => .equal a b
  | .less a b => .less a b
  | .negative p => .negative (translate p)
  | .conjunction p q => .conjunction (translate p) (translate q)
  | .disjunction p q => .negative (.conjunction (.negative (translate p)) (.negative (translate q)))

def existsPrefix (ν : Nat → Nat) : List Nat → BaseFormula.Formula → Prop
  | [], p => p.eval ν
  | i :: xs, p => ∃ n : Nat, existsPrefix (Function.update ν i n) xs p

def forallPrefix (ν : Nat → Nat) : List Nat → BaseFormula.Formula → Prop
  | [], p => p.eval ν
  | i :: xs, p => ∀ n : Nat, forallPrefix (Function.update ν i n) xs p

namespace Code
def step (op : CommonHeadCompiler.Instruction) (stack : List Nat) : List Nat :=
  if op.1 = 0 then 1 :: stack
  else if op.1 = 1 then 0 :: stack
  else if op.1 = 2 then (5 * Nat.pair op.2.1 op.2.2) :: stack
  else if op.1 = 3 then (5 * Nat.pair op.2.1 op.2.2 + 1) :: stack
  else if op.1 = 4 then (5 * (5 * Nat.pair op.2.2 (4 * op.2.1) + 1) + 2) :: stack
  else if op.1 = 5 then (5 * stack.headD 1 + 2) :: stack.tail
  else if op.1 = 6 then (5 * Nat.pair (stack.tail.headD 1) (stack.headD 1) + 3) :: stack.tail.tail
  else if op.1 = 7 then
    (5 * (5 * Nat.pair (5 * stack.tail.headD 1 + 2) (5 * stack.headD 1 + 2) + 3) + 2) :: stack.tail.tail
  else 1 :: stack

def run (code : List CommonHeadCompiler.Instruction) (stack : List Nat) : List Nat :=
  code.foldl (fun s op => step op s) stack
def compile (code : List CommonHeadCompiler.Instruction) : Nat := (run code []).headD 1

def decideExists (xs values : List Nat) (code : List CommonHeadCompiler.Instruction) : Option Bool :=
  SourceParameterDecision.Code.decideExists xs values (compile code)
def decideForall (xs values : List Nat) (code : List CommonHeadCompiler.Instruction) : Option Bool :=
  SourceParameterDecision.Code.decideForall xs values (compile code)
def decideClosureExists (code : List CommonHeadCompiler.Instruction) : Option Bool :=
  SourceBooleanPrograms.Code.decideExists (compile code)
def decideClosureForall (code : List CommonHeadCompiler.Instruction) : Option Bool :=
  SourceBooleanPrograms.Code.decideForall (compile code)
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSource
