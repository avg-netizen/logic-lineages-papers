module

public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalListDefinitions

@[expose] public section
/-! Uniform Π₂ matrices for actual ordinary-program predicates used by
paper14 lem:list. Matrix normal forms alone do not supply a Turing jump. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionProgramMatrices
open PredictionLearning

def totalMatrix (c : Code) (input fuel : Nat) : Bool :=
  (Nat.Partrec.Code.evaln fuel c input).isSome

def observedAgreement (observation response : Option Nat) : Bool :=
  match observation with
  | none => true
  | some v => decide (response = some v)

def equalityMatrix (c d : Code) (query certificate : Nat) : Bool :=
  let input := query.unpair.1
  let stage := query.unpair.2
  observedAgreement (Nat.Partrec.Code.evaln stage c input) (Nat.Partrec.Code.evaln certificate d input) &&
    observedAgreement (Nat.Partrec.Code.evaln stage d input) (Nat.Partrec.Code.evaln certificate c input)

end LogicLineages.ComputabilityKnowledge.PredictionProgramMatrices
