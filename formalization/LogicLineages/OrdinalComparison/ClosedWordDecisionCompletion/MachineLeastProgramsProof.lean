module
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineProgramsProof
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineTerminationProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerLeastProgramsProof
public import Mathlib.Computability.RE

@[expose] public section
namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachinePrograms
open Machine RankedWordDecisionCompletion
attribute [local irreducible] Computable Partrec Nat.unpair Nat.sqrt leastSteps run

theorem stopped_computable : Computable (fun p : Nat × Nat × Nat × Nat × Nat =>
    stopped p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) :=
  Primrec.or.to_comp.comp (Computable.fst.comp run_computable)
    (RunnerCode.isEmpty_primitive.to_comp.comp (Computable.snd.comp run_computable))

attribute [local irreducible] stopped

theorem leastSteps_computable : Computable (fun p : Nat × Nat × Nat × Nat =>
    leastSteps p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let A := Nat × Nat × Nat × Nat
  have hs : Computable (fun p : A × Nat =>
      stopped p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2) :=
    stopped_computable.comp ((Computable.fst.comp Computable.fst).pair
      ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
        ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))).pair
          ((Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))).pair
            Computable.snd))))
  have hp : ComputablePred (fun p : A × Nat =>
      stopped p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2 = true) := by
    have hd : Computable (fun p : A × Nat => decide
        (stopped p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2 = true)) := by simpa using hs
    exact hd.computablePred
  have hex : ∀ p : A, ∃ steps, stopped p.1 p.2.1 p.2.2.1 p.2.2.2 steps = true :=
    fun p => MachineProof.allInputTermination p.1 p.2.1 p.2.2.1 p.2.2.2
  apply (Computable.find hp hex).of_eq
  intro p
  have he : leastSteps p.1 p.2.1 p.2.2.1 p.2.2.2 = Nat.find (hex p) := by
    simp [leastSteps,hex p]
  exact he.symm

theorem solveWithFuel_computable : Computable (fun p : Nat × Nat × Nat × Nat =>
    solveWithFuel p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hfuel : Computable (fun p : Nat × Nat × Nat × Nat => p.2.1) :=
    Computable.fst.comp Computable.snd
  have hfloor : Computable (fun p : Nat × Nat × Nat × Nat => p.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hcode : Computable (fun p : Nat × Nat × Nat × Nat => p.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  exact Computable.fst.comp (run_computable.comp
    (Computable.fst.pair (hfuel.pair (hfloor.pair (hcode.pair leastSteps_computable)))))

attribute [local irreducible] solveWithFuel

theorem solve_computable : Computable (fun p : Nat × Nat => solve p.1 p.2) :=
  solveWithFuel_computable.comp
    ((Primrec.nat_max.to_comp.comp (Computable.const 3) Computable.fst).pair
      ((Primrec.list_length.to_comp.comp (CodePrograms.names_primitive.to_comp.comp Computable.snd)).pair
        ((Computable.const 0).pair Computable.snd)))

theorem uniformNumericSolver : MachineTargets.UniformNumericSolver :=
  ⟨leastSteps_computable,solveWithFuel_computable,solve_computable⟩

#print axioms stopped_computable
#print axioms leastSteps_computable
#print axioms solveWithFuel_computable
#print axioms solve_computable
#print axioms uniformNumericSolver

end LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachinePrograms
