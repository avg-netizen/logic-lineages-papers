module

public import LogicLineages.ComputabilityKnowledge.PredictionProgramMatricesDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionProgramMatricesTargets
open PredictionLearning PredictionCanonicalList PredictionProgramMatrices

def PrimitiveRecursiveTotalMatrix : Prop :=
  Primrec (fun z : Code × Nat × Nat => totalMatrix z.1 z.2.1 z.2.2)

def ExactTotalityMatrix : Prop :=
  ∀ c : Code, TotalNat c ↔ ∀ input : Nat, ∃ fuel : Nat, totalMatrix c input fuel = true

def PrimitiveRecursiveEqualityMatrix : Prop :=
  Primrec (fun z : (Code × Code) × Nat × Nat => equalityMatrix z.1.1 z.1.2 z.2.1 z.2.2)

def ExactExtensionalEqualityMatrix : Prop :=
  ∀ c d : Code, SameFunction c d ↔ ∀ query : Nat, ∃ certificate : Nat,
    equalityMatrix c d query certificate = true

end LogicLineages.ComputabilityKnowledge.PredictionProgramMatricesTargets
