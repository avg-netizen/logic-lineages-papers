module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadClosureDecisionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadBoolean

/-- Boolean combinations of original raw common-head comparisons under one
fixed head list and one raw valuation. Atom operands are unchanged source codes. -/
inductive Formula where
  | truth | falsity
  | equal (left right : Nat) | less (left right : Nat)
  | negative (body : Formula)
  | conjunction (left right : Formula) | disjunction (left right : Formula)

noncomputable def Formula.eval (heads : List Nat) (ν : Nat → Nat) : Formula → Prop
  | .truth => True
  | .falsity => False
  | .equal a b => CommonLayerSyntax.codedValue heads a ν = CommonLayerSyntax.codedValue heads b ν
  | .less a b => CommonLayerSyntax.codedValue heads a ν < CommonLayerSyntax.codedValue heads b ν
  | .negative p => ¬p.eval heads ν
  | .conjunction p q => p.eval heads ν ∧ q.eval heads ν
  | .disjunction p q => p.eval heads ν ∨ q.eval heads ν

def Formula.encode : Formula → List CommonHeadCompiler.Instruction
  | .truth => [(1,0,0)]
  | .falsity => [(0,0,0)]
  | .equal a b => [(2,a,b)]
  | .less a b => [(3,a,b)]
  | .negative p => CommonHeadCode.negative p.encode
  | .conjunction p q => CommonHeadCode.conjunction p.encode q.encode
  | .disjunction p q => CommonHeadCode.disjunction p.encode q.encode

noncomputable def translate (heads : List Nat) : Formula → BaseFormula.Formula
  | .truth => .truth
  | .falsity => .falsity
  | .equal a b => CommonLayerComparison.compile heads a b 0
  | .less a b => CommonLayerComparison.compile heads a b (-1)
  | .negative p => .negative (translate heads p)
  | .conjunction p q => .conjunction (translate heads p) (translate heads q)
  | .disjunction p q => .disjunction (translate heads p) (translate heads q)

noncomputable def existsPrefix (heads : List Nat) (ν : Nat → Nat) : List Nat → Formula → Prop
  | [], p => p.eval heads ν
  | i :: xs, p => ∃ n : Nat, existsPrefix heads (Function.update ν i n) xs p
noncomputable def forallPrefix (heads : List Nat) (ν : Nat → Nat) : List Nat → Formula → Prop
  | [], p => p.eval heads ν
  | i :: xs, p => ∀ n : Nat, forallPrefix heads (Function.update ν i n) xs p

namespace Code
abbrev Program := List CommonHeadCompiler.Instruction
abbrev Stack := List Program

def head (stack : Stack) : Program := stack.headD [(0,0,0)]
noncomputable def step (heads : List Nat) (op : CommonHeadCompiler.Instruction) (stack : Stack) : Stack :=
  if op.1 = 0 then [(0,0,0)] :: stack
  else if op.1 = 1 then [(1,0,0)] :: stack
  else if op.1 = 2 then CommonLayerComparison.compileCode heads op.2.1 op.2.2 0 :: stack
  else if op.1 = 3 then CommonLayerComparison.compileCode heads op.2.1 op.2.2 (-1) :: stack
  else if op.1 = 5 then CommonHeadCode.negative (head stack) :: stack.tail
  else if op.1 = 6 then CommonHeadCode.conjunction (head stack.tail) (head stack) :: stack.tail.tail
  else if op.1 = 7 then CommonHeadCode.disjunction (head stack.tail) (head stack) :: stack.tail.tail
  else [(0,0,0)] :: stack
noncomputable def run (heads : List Nat) (code : Program) (stack : Stack) : Stack :=
  code.foldl (fun s op => step heads op s) stack
noncomputable def compile (heads : List Nat) (code : Program) : Program := head (run heads code [])

noncomputable def decideExists (heads xs values : List Nat) (code : Program) : Option Bool :=
  BaseBooleanSource.Code.decideExists xs values (compile heads code)
noncomputable def decideForall (heads xs values : List Nat) (code : Program) : Option Bool :=
  BaseBooleanSource.Code.decideForall xs values (compile heads code)
noncomputable def decideClosureExists (heads : List Nat) (code : Program) : Option Bool :=
  BaseBooleanSource.Code.decideClosureExists (compile heads code)
noncomputable def decideClosureForall (heads : List Nat) (code : Program) : Option Bool :=
  BaseBooleanSource.Code.decideClosureForall (compile heads code)
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadBoolean
