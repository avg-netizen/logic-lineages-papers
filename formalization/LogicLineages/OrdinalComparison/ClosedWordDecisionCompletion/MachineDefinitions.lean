module
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinearDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.Machine
open WordLinearDecisionCompletion
open LayeredComparison.SnyatkovCompletion

/-- This existing literal constant evaluator is used only when no raw name
occurs. It never evaluates a nonlinear word or invents its value. -/
def constant (code : Nat) : Bool :=
  ClosedLinear.Code.evaluateConstants (WordLinearDecisionCompletion.Code.liftFormula 0 code)

/-- Semantic finite-depth reference, not a uniform-computability shortcut. -/
noncomputable def fuelValue (D : Nat) : Nat → Nat → Nat → Bool
  | 0, _, code => if Code.names code = [] then constant code else false
  | fuel+1, floor, code =>
      if Code.names code = [] then constant code
      else (Code.children D floor code).any (fun b => fuelValue D fuel b.1 b.2)

/-- A natural-valued auxiliary termination measure. Its computability is not
assumed or needed. Every expanded child has one less literal fuel. -/
noncomputable def treeSize (D : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | fuel+1, floor, code =>
      if Code.names code = [] then 1
      else 1 + ((Code.children D floor code).map (fun b => treeSize D fuel b.1 b.2)).sum

/-- (remaining raw-name fuel, inherited introduction floor, formula code). -/
abbrev Work := Nat × Nat × Nat
abbrev State := Bool × List Work

def initial (fuel floor code : Nat) : State := (false,[(fuel,floor,code)])

/-- One finite OR-worklist transition. No valuation, consistency test,
well-founded-recursion oracle or result of a recursive query is an input. -/
noncomputable def step (D : Nat) (s : State) : State :=
  if s.1 then s else
    match s.2 with
    | [] => s
    | (fuel,floor,code)::rest =>
        if Code.names code = [] then (constant code,rest)
        else if fuel = 0 then (false,rest)
        else (false,(Code.children D floor code).map
          (fun b => (fuel-1,b.1,b.2)) ++ rest)

noncomputable def run (D fuel floor code steps : Nat) : State :=
  (step D)^[steps] (initial fuel floor code)

noncomputable def stopped (D fuel floor code steps : Nat) : Bool :=
  let s := run D fuel floor code steps
  s.1 || s.2.isEmpty

/-- Actual unbounded least-stopping search. Totality and UNIFORM numerical
computability must be proved; the default is not evidence of termination. -/
noncomputable def leastSteps (D fuel floor code : Nat) : Nat := by
  classical
  exact if h : ∃ steps, stopped D fuel floor code steps = true then Nat.find h else 0

noncomputable def solveWithFuel (D fuel floor code : Nat) : Bool :=
  (run D fuel floor code (leastSteps D fuel floor code)).1

/-- Initial fuel is the computable count of actual distinct raw names.
Raising D to at least three adds no assumption to the original finite-degree
language. The internal floor starts at zero, so the original domains remain. -/
noncomputable def solve (D code : Nat) : Bool :=
  solveWithFuel (max 3 D) (Code.names code).length 0 code

end LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.Machine
