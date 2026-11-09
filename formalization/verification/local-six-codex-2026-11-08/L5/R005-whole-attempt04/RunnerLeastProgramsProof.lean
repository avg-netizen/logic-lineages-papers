module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerProgramsProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerTerminationProof
public import Mathlib.Computability.RE

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerCode
open PolynomialGraphCompletion AlgorithmPrograms
attribute [local irreducible] Computable Partrec Nat.unpair Nat.sqrt Runner.leastFuel

theorem isEmpty_primitive {β : Type} [Primcodable β] : Primrec (fun xs : List β => xs.isEmpty) := by
  apply (Primrec.beq.comp Primrec.list_length (Primrec.const 0)).of_eq
  intro xs
  cases xs <;> simp

theorem stopped_computable : Computable (fun p : Nat × Nat × Row × Nat =>
    Runner.stopped p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let A := Nat × Nat × Row × Nat
  have hD : Computable (fun p : A => p.1) := Computable.fst
  have hr : Computable (fun p : A => p.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have ha := admitted_primitive.to_comp.comp hD hr
  have hempty := isEmpty_primitive.to_comp.comp (Computable.fst.comp (Computable.snd.comp run_computable))
  apply (Primrec.or.to_comp.comp (Primrec.not.to_comp.comp ha) hempty).of_eq
  intro p
  simp [Runner.stopped,run_calibration,Runner.encodeState]

theorem leastFuel_computable : RunnerTargets.LeastFuelProgram := by
  let A := Nat × Nat × Row
  have hs : Computable (fun p : A × Nat => Runner.stopped p.1.1 p.1.2.1 p.1.2.2 p.2) :=
    stopped_computable.comp ((Computable.fst.comp Computable.fst).pair
      ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
        ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair Computable.snd)))
  have hp : ComputablePred (fun p : A × Nat => Runner.stopped p.1.1 p.1.2.1 p.1.2.2 p.2 = true) := by
    have hd : Computable (fun p : A × Nat => decide
        (Runner.stopped p.1.1 p.1.2.1 p.1.2.2 p.2 = true)) := by simpa using hs
    exact hd.computablePred
  have hex : ∀ p : A, ∃ fuel, Runner.stopped p.1 p.2.1 p.2.2 fuel = true :=
    fun p => RunnerProof.allInputTermination p.1 p.2.1 p.2.2
  apply (Computable.find hp hex).of_eq
  intro p
  have he : Runner.leastFuel p.1 p.2.1 p.2.2 = Nat.find (hex p) := by
    simp [Runner.leastFuel,hex p]
  exact he.symm

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerCode
