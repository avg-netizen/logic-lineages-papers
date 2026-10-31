module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeGameDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionTapePolicyCompilerDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionFlipMaskDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeFlip
open PredictionFiniteChange PredictionSelfHistory

def flipRule (R : Matrix) (b : Nat → Nat) (z : Nat) : PairedRule :=
  fun xs ys => if PredictionFlipMask.flipEvent R z xs then !(PredictionTapeGame.budgetRule b xs ys)
    else PredictionTapeGame.budgetRule b xs ys

def flipPolicy (R : Matrix) (b : Nat → Nat) (z : Nat) : PredictionGame.Policy :=
  selfPolicy (flipRule R b z)

end LogicLineages.ComputabilityKnowledge.PredictionTapeFlip
