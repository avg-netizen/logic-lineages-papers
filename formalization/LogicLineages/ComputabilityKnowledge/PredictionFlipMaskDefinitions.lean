module

public import LogicLineages.ComputabilityKnowledge.PredictionFiniteChangeDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionCodeEvaderDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionBaselineGameDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionFlipMask
open PredictionFiniteChange PredictionCodeEvader PredictionBaselineGame PredictionSelfHistory

def flipEvent (R : Matrix) (z : Nat) (xs : List Bool) : Bool :=
  match completedCode xs with
  | none => false
  | some k => changeEvent R z k xs.length

def flipRule (R : Matrix) (b : Nat → Nat) (z : Nat) : PairedRule :=
  fun xs ys => if flipEvent R z xs then !(budgetRule b xs ys) else budgetRule b xs ys

def flipPolicy (R : Matrix) (b : Nat → Nat) (z : Nat) : PredictionGame.Policy :=
  selfPolicy (flipRule R b z)

end LogicLineages.ComputabilityKnowledge.PredictionFlipMask
