module

public import LogicLineages.ComputabilityKnowledge.OracleDerivationDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OracleDerivationTargets
open OracleProgram OracleDerivation

def FiniteDerivationSound : Prop :=
  ∀ (g : Nat → Nat) (p : Program) (input output : Nat), Derives g p input output →
    output ∈ eval (fun n => Part.some (g n)) p input

def FiniteDerivationComplete : Prop :=
  ∀ (g : Nat → Nat) (p : Program) (input output : Nat),
    output ∈ eval (fun n => Part.some (g n)) p input → Derives g p input output

def FiniteDerivationUnique : Prop :=
  ∀ (g : Nat → Nat) (p : Program) (input left right : Nat),
    Derives g p input left → Derives g p input right → left = right

end LogicLineages.ComputabilityKnowledge.OracleDerivationTargets
