module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerTargets
open PolynomialGraphCompletion Runner

/-- Total termination of the concrete actual work-stack machine, with its
explicit immediate invalid branch. No termination premise is an input. -/
def AllInputTermination : Prop := ∀ D maximum r,
  ∃ fuel : Nat, stopped D maximum r fuel = true

def ExactLeastStopping : Prop := ∀ D maximum r,
  stopped D maximum r (leastFuel D maximum r) = true ∧
  (∀ n, n < leastFuel D maximum r → stopped D maximum r n = false) ∧
  (admitted D r = false → leastFuel D maximum r = 0)

def FiniteRunnerProgram : Prop :=
  Computable (fun input : Nat × Nat × Row × Nat =>
    encodeState (run input.1 input.2.1 input.2.2.1 input.2.2.2))

def LeastFuelProgram : Prop :=
  Computable (fun input : Nat × Nat × Row =>
    leastFuel input.1 input.2.1 input.2.2)

def ExactSingleRowPackage : Prop := ∀ D maximum r, 3 ≤ D → RowAllowed D r →
  PackageCorrect D maximum [r] (solve D maximum r)

def ExactFamilyPackage : Prop := ∀ D maximum rows,
  3 ≤ D → (∀ r ∈ rows, RowAllowed D r) →
    PackageCorrect D maximum rows (compile D maximum rows)

def ActualFamilyProgram : Prop :=
  Computable (fun input : Nat × Nat × List Row =>
    encodePackage (compile input.1 input.2.1 input.2.2))

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerTargets
