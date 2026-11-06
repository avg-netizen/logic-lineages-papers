module
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.RunnerProgramsProof
import LogicLineages.OrdinalComparison.FullWordGuardCompletion.RunnerProof
import Mathlib.Computability.RE

@[expose] public section
namespace LogicLineages.OrdinalComparison.FullWordGuardCompletion.LeastFuelProgramsProof
open GuardChildMeasureCompletion

attribute [local irreducible] Computable Partrec Nat.unpair Nat.sqrt leastFuel

theorem leastFuel_computable :
    Computable (fun p : Nat × WordPair => leastFuel p.1 p.2) := by
  have hs : Computable (fun p : (Nat × WordPair) × Nat =>
      stopped p.1.1 p.1.2 p.2) :=
    (RunnerProgramsProof.stopped_primitive.comp
      ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))).to_comp
  have hp : ComputablePred (fun p : (Nat × WordPair) × Nat =>
      stopped p.1.1 p.1.2 p.2 = true) := by
    have hd : Computable (fun p : (Nat × WordPair) × Nat =>
        decide (stopped p.1.1 p.1.2 p.2 = true)) := by
      simpa using hs
    exact hd.computablePred
  have hex : ∀ p : Nat × WordPair, ∃ fuel : Nat, stopped p.1 p.2 fuel = true :=
    fun p => RunnerProof.runnerTerminates p.1 p.2
  exact (Computable.find hp hex).of_eq
    (fun p => (RunnerProof.leastFuel_eq p.1 p.2).symm)

theorem leastFuelProgram : RunnerTargets.LeastFuelProgram := leastFuel_computable

end LogicLineages.OrdinalComparison.FullWordGuardCompletion.LeastFuelProgramsProof
