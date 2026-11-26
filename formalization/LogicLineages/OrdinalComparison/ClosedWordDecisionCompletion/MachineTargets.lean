module
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineTargets
open WordLinearDecisionCompletion Machine

def ExactConstantEvaluation : Prop := ∀ floor (p : Formula), names p = [] →
  (constant (Formula.encode p) = true ↔ SatisfiableAt floor p)

/-- Total termination includes malformed codes and insufficient input fuel. -/
def AllInputTermination : Prop := ∀ D fuel floor code : Nat,
  ∃ steps : Nat, stopped D fuel floor code steps = true

def ExactLeastStopping : Prop := ∀ D fuel floor code : Nat,
  stopped D fuel floor code (leastSteps D fuel floor code) = true ∧
  ∀ n, n < leastSteps D fuel floor code → stopped D fuel floor code n = false

/-- Uniform finite-step execution, including runtime fuel and code. -/
def ActualTransitionPrograms : Prop :=
  Primrec constant ∧
  Computable (fun input : Nat × State => step input.1 input.2) ∧
  Computable (fun input : Nat × Nat × Nat × Nat × Nat =>
    run input.1 input.2.1 input.2.2.1 input.2.2.2.1 input.2.2.2.2)

def ExactFiniteDepth : Prop := ∀ D fuel floor code : Nat,
  solveWithFuel D fuel floor code = fuelValue D fuel floor code

/-- Actual raw-name decrease, not a caller-supplied termination hypothesis,
pays adequate fuel for every original admitted closed existential matrix. -/
def AdequateFuelCorrectness : Prop := ∀ D fuel floor (p : Formula),
  3 ≤ D → Formula.allowed D p → (names p).length ≤ fuel →
    (solveWithFuel D fuel floor (Formula.encode p) = true ↔ SatisfiableAt floor p)

/-- One total computable numerical solver, not a family at fixed fuel. -/
def UniformNumericSolver : Prop :=
  Computable (fun input : Nat × Nat × Nat × Nat =>
    leastSteps input.1 input.2.1 input.2.2.1 input.2.2.2) ∧
  Computable (fun input : Nat × Nat × Nat × Nat =>
    solveWithFuel input.1 input.2.1 input.2.2.1 input.2.2.2) ∧
  Computable (fun input : Nat × Nat => solve input.1 input.2)

def ActualClosedDecision : Prop := ∀ D (p : Formula), Formula.allowed D p →
  (solve D (Formula.encode p) = true ↔
    ∃ ν : Nat → Nat, Formula.meaningful p ν ∧ Formula.eval ν p)

/-- ENTIRE printed paper08 thm:existential. The solver is a construction
obligation. There is no row, residue, branch, bound, termination or semantic
oracle premise, and every literal word domain remains globally explicit. -/
def FullClosedExistentialWordArithmetic : Prop :=
  ∃ solver : Nat → Nat → Bool,
    Computable (fun input : Nat × Nat => solver input.1 input.2) ∧
    ∀ D (p : Formula), Formula.allowed D p →
      (solver D (Formula.encode p) = true ↔
        ∃ ν : Nat → Nat, Formula.meaningful p ν ∧ Formula.eval ν p)

end LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineTargets
