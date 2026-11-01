module
public import LogicLineages.OrdinalComparison.ComparisonAssemblyDefinitions
public import LogicLineages.OrdinalComparison.PositiveInputPlugDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

inductive OneInputOrderRelation where
  | equal | weak | strict
  deriving DecidableEq

def oneInputOrderRelationCode : OneInputOrderRelation → Nat
  | .equal => 0
  | .weak => 1
  | .strict => 2

def oneInputOrderBool (relation a b : Nat) : Bool :=
  if relation=0 then decide (a=b) else if relation=1 then decide (a≤b) else decide (a<b)

inductive OneInputBooleanExpr where
  | truth (value : Bool)
  | atom (relation : OneInputOrderRelation) (left right : FixedLimitPositiveExpr)
  | neg (formula : OneInputBooleanExpr)
  | conj (left right : OneInputBooleanExpr)
  | disj (left right : OneInputBooleanExpr)

def oneInputBooleanValid : OneInputBooleanExpr → Prop
  | .truth _ => True
  | .atom _ E F => fixedLimitProfileBelow epsilonZero E ∧ fixedLimitProfileBelow epsilonZero F
  | .neg formula => oneInputBooleanValid formula
  | .conj left right | .disj left right => oneInputBooleanValid left ∧ oneInputBooleanValid right

noncomputable def actualOneInputBooleanValue : OneInputBooleanExpr → Nat → Bool
  | .truth b, _ => b
  | .atom r E F, x => oneInputOrderBool (oneInputOrderRelationCode r)
      (actualFixedLimitProfileEval E x) (actualFixedLimitProfileEval F x)
  | .neg formula, x => !(actualOneInputBooleanValue formula x)
  | .conj left right, x => actualOneInputBooleanValue left x && actualOneInputBooleanValue right x
  | .disj left right, x => actualOneInputBooleanValue left x || actualOneInputBooleanValue right x

abbrev OneInputBooleanInstruction := Nat × Nat × Nat

/-- Literal finite postfix compilation, preserving every original positive
expression for exact evaluation in the exceptional prefix. -/
def oneInputBooleanCompile : OneInputBooleanExpr → List OneInputBooleanInstruction
  | .truth b => [(if b then 1 else 0,0,0)]
  | .atom r E F => [(2+oneInputOrderRelationCode r,positiveExprEncode E,positiveExprEncode F)]
  | .neg formula => oneInputBooleanCompile formula++[(5,0,0)]
  | .conj left right => oneInputBooleanCompile left++oneInputBooleanCompile right++[(6,0,0)]
  | .disj left right => oneInputBooleanCompile left++oneInputBooleanCompile right++[(7,0,0)]

noncomputable def encodedOneInputBooleanStep (x : Nat) (instruction : OneInputBooleanInstruction)
    (stack : List Bool) : List Bool :=
  if instruction.1=0 then false::stack
  else if instruction.1=1 then true::stack
  else if instruction.1 ≤ 4 then
    oneInputOrderBool (instruction.1-2)
      (encodedPositiveEvaluation instruction.2.1 x) (encodedPositiveEvaluation instruction.2.2 x)::stack
  else if instruction.1=5 then (!stack.headD false)::stack.tail
  else if instruction.1=6 then (stack.tail.headD false && stack.headD false)::stack.tail.tail
  else if instruction.1=7 then (stack.tail.headD false || stack.headD false)::stack.tail.tail
  else false::stack

noncomputable def encodedOneInputBooleanRun (program : List OneInputBooleanInstruction) (x : Nat) (stack : List Bool) : List Bool :=
  program.foldl (fun stack instruction => encodedOneInputBooleanStep x instruction stack) stack

noncomputable def encodedOneInputBooleanValue (program : List OneInputBooleanInstruction) (x : Nat) : Bool :=
  (encodedOneInputBooleanRun program x []).headD false

noncomputable def encodedOneInputBooleanInstructionTail (instruction : OneInputBooleanInstruction) : Nat :=
  if 2 ≤ instruction.1 ∧ instruction.1 ≤ 4 then
    (encodedOneVariableSignDecision (2*instruction.2.1) (2*instruction.2.2)).2
  else 1

noncomputable def encodedOneInputBooleanTail (program : List OneInputBooleanInstruction) : Nat :=
  (program.map encodedOneInputBooleanInstructionTail).foldr max 1

/-- The positive prefix INCLUDES the proved tail point. Thus this single
finite literal-source evaluation covers existential and universal closure. -/
noncomputable def encodedOneInputBooleanClosures (program : List OneInputBooleanInstruction) : Bool × Bool :=
  let points := ((List.range (encodedOneInputBooleanTail program+1)).drop 1)
  (points.any (encodedOneInputBooleanValue program),points.all (encodedOneInputBooleanValue program))

end LogicLineages.OrdinalComparison
