module
public import LogicLineages.OrdinalComparison.SourceGammaWeakCodedReductionDefinitions
public import LogicLineages.OrdinalComparison.SourceGammaCounterexampleDefinitions
public import LogicLineages.OrdinalComparison.ParametricRestrictedSourceEvaluatorDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaWeakCounterexample
def positive (xs : List Nat) : Bool := SourceGammaCounterexample.positive xs
def compareResults : Option Nat → Option Nat → Bool
  | some left,some right => decide (right<left)
  | _,_ => false
noncomputable def counterexample (b code : Nat) (xs : List Nat) : Bool :=
  if SourceRestrictedSyntaxChecker.restrictedCode code=false then true else
  match SourceMachineQueryCode.unpack code with
  | none => false
  | some (n,left,right) =>
      if xs.length=n ∧ positive xs=true then
        compareResults (ParametricRestrictedSourceEvaluator.gammaEvaluate b n left xs)
          (ParametricRestrictedSourceEvaluator.gammaEvaluate b n right xs)
      else false
end LogicLineages.OrdinalComparison.Source.SourceGammaWeakCounterexample
