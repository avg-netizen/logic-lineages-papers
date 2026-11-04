module
public import LogicLineages.OrdinalComparison.SourceMachineHaltingConjunctionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceMachineHaltingConjunction.Targets

def EffectiveArguments : Prop :=
  Primrec coefficient ∧ Primrec oddConstant ∧
  Primrec (fun p : Nat×Nat×Nat => argument p.1 p.2.1 p.2.2) ∧
  ∀ b e t : Nat, 5 ≤ argument b e t ∧ b < argument b e t ∧
    t ≤ argument b e t ∧ PerturbedControl.valuationTwo (argument b e t) = e

def ExactFixedWitness : Prop := ∀ b e t : Nat,
  ((∃ z y w : Nat, Conjunction b e t z y w) ↔
    SourceBlankMachineSimulation.boundedH (e,argument b e t) = true) ∧
  (SourceBlankMachineSimulation.boundedH (e,argument b e t) = true →
    Conjunction b e t (argument b e t-4)
      (SourceMachineControlNonperiodicity.gamma b (argument b e t))
      ((SourceMachineControlNonperiodicity.gamma b (argument b e t)-1)/2))

def ExactHaltingReduction : Prop := ∀ b e : Nat,
  Satisfiable b e ↔ SourceBlankMachineSimulation.Halts e
end LogicLineages.OrdinalComparison.SourceMachineHaltingConjunction.Targets
