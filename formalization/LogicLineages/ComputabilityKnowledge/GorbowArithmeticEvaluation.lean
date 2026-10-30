module

public import LogicLineages.ComputabilityKnowledge.GorbowSortedBooleanCode

@[expose] public section
/-! Executable evaluation only for closed arithmetic syntax. Full-language u
has arbitrary interpretation and is not evaluated by this program. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowArithmeticEvaluation

def step (state : Option (List Nat)) (tag : Nat) : Option (List Nat) := do
  let stack ← state
  if tag=1 then some (0::stack)
  else if tag=2 then
    if stack.length≥1 then some ((stack.getD 0 0+1)::stack.drop 1) else none
  else if tag=3 then
    if stack.length≥2 then some ((stack.getD 0 0+stack.getD 1 0)::stack.drop 2) else none
  else if tag=4 then
    if stack.length≥2 then some ((stack.getD 0 0*stack.getD 1 0)::stack.drop 2) else none
  else none

def run (raw stack : List Nat) : Option (List Nat) :=
  raw.reverse.foldl step (some stack)

def rawValue (raw : List Nat) : Option Nat :=
  if GorbowClosedTermCode.arithmeticRaw raw then do
    let stack ← run raw []
    if stack.length=1 then some (stack.getD 0 0) else none
  else none

def sortedValue (code : Nat) : Option Nat := do
  let raw ← GorbowSortedSyntaxCode.decodeTermRaw code
  rawValue raw
end LogicLineages.ComputabilityKnowledge.GorbowArithmeticEvaluation
