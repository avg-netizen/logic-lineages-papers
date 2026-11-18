module
public import LogicLineages.ControlSensitivityCurrent.CurrentCounterBoundDefinitions
public import LogicLineages.ControlSensitivityCurrent.FullAdditionTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentCounterBoundTargets

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open CurrentCounterBound
open OriginalInput (Query decode)

def PointCalibration : Prop :=
  ∀ p f, FullAddition.Targets.SourceGrowth f →
    ∀ (q : Query) xs, xs.length = q.1 → (test p f q xs = true ↔ Point p f q xs)

def Effective : Prop :=
  ∀ p : AdmissibleSum.Policy, PolicyShape.Effective p →
    ∀ f : Nat → Nat, Computable f → FullAddition.Targets.SourceGrowth f →
      Computable (fun x : Query × List Nat => test p f x.1 x.2)

def Full : Prop :=
  ∀ p : AdmissibleSum.Policy, PolicyShape.Effective p →
    ∀ f : Nat → Nat, Computable f → FullAddition.Targets.SourceGrowth f →
      REPred (fun n => ¬ codedGood p f n) ∧
      ((∃ d : DecidablePred (codedGood p f), Computable fun n => @decide (codedGood p f n) (d n)) ↔
        CoordinateBound p f)

end LogicLineages.ControlSensitivityCurrent.CurrentCounterBoundTargets
