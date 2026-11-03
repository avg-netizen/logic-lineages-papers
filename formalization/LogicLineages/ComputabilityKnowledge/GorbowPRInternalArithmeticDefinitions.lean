module

public import LogicLineages.ComputabilityKnowledge.GorbowPRInternalCoherenceDefinitions

@[expose] public section
/-! Fixed literal primitive-recursive ASTs for the arithmetic operations used
by the source registry tuple convention. Their symbolic correctness is a
separate internal theorem, not inferred from standard evaluation calibration.
The recursion input is first: addition[y,x]=x+y, multiplication[y,x]=x*y. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPRInternalArithmetic
open GorbowPRProgram

def additionBase : Program 1 := .projection 0
def additionStep : Program 3 :=
  .composition .succ (fun _ : Fin 1 => .projection (1 : Fin 3))
def addition : Program 2 := .recursion additionBase additionStep

def multiplicationBase : Program 1 := .composition .zero Fin.elim0
def multiplicationStep : Program 3 :=
  .composition addition (fun i : Fin 2 =>
    if i.val = 0 then .projection (2 : Fin 3) else .projection (1 : Fin 3))
def multiplication : Program 2 := .recursion multiplicationBase multiplicationStep

/-- Input order is now the source pair convention [a,b]. -/
def sumInputs : Program 2 :=
  .composition addition (fun i : Fin 2 =>
    if i.val = 0 then .projection (1 : Fin 2) else .projection (0 : Fin 2))
def squareSum : Program 2 :=
  .composition multiplication (fun _ : Fin 2 => sumInputs)
def pairing : Program 2 :=
  .composition addition (Fin.cases (.projection (0 : Fin 2)) (fun _ : Fin 1 => squareSum))

end LogicLineages.ComputabilityKnowledge.GorbowPRInternalArithmetic
