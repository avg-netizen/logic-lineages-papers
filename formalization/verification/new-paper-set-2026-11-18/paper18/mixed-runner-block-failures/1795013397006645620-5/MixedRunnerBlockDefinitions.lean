module
public import LogicLineages.StandardControlCurrent.HyperCloseBlockDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ReverseWindowDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ActiveHyperDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.MixedRunnerBlock
open OrdinalComparison LayeredComparison.SnyatkovCompletion
open HyperCloseBlock (existsNames)

/-- Actual shared-update block contract, not a caller-supplied projection premise. -/
def Reduction (xs : List Nat) (x : Nat) (before after : Matrix) : Prop :=
  xs.Nodup → x ∈ xs →
  (∀ ν, existsNames xs before ν ↔ existsNames (xs.erase x) after ν) ∧
  (xs.erase x).Nodup ∧ (xs.erase x).length+1=xs.length ∧
  (xs.erase x).length<xs.length ∧
  ∀ name, name ∈ after.variables → name ∉ xs.erase x →
    name ∈ before.variables ∧ name ∉ xs

abbrev ReverseInput := List Nat × ReverseWindow.Code.Input
abbrev LinearInput := List Nat × LinearWindow.Code.Input
abbrev ActiveInput := List Nat × ActiveHyper.Code.Input

def reverseProgram (q : ReverseInput) : List Nat × Nat :=
  (q.1.erase q.2.1, ReverseWindow.Code.finiteCases q.2)
def linearProgram (q : LinearInput) : List Nat × Nat :=
  (q.1.erase (LinearWindow.Code.rightName q.2), LinearWindow.Code.finiteCases q.2)
def activeProgram (q : ActiveInput) : List Nat × Nat :=
  (q.1.erase (ActiveHyper.Code.rightName q.2), ActiveHyper.Code.finiteCases q.2)
end LogicLineages.StandardControlCurrent.MixedRunnerBlock
