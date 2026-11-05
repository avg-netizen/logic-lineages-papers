module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiParametersDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.BaseTermProgramsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiPrograms.Code

/-- Pad the original zero-default ambient values through every actual term
name before calling the existing evaluator, whose outside default is one. -/
def bound (code : Nat) : Nat := SourceRows.Code.bound (SourceTermGraph.Code.instructions code)
def table (values : List Nat) (code : Nat) : List Nat :=
  (List.range (bound code)).map (fun i => values.getD i 0)
def value (values : List Nat) (code : Nat) : Nat := BaseTermPrograms.valueCode code (table values code)

def termTest (boundNames : List Nat) (code : Nat) : Bool :=
  if code % 4 = 0 ∨ code % 4 = 1 then true
  else if code % 4 = 2 then termTest boundNames (code / 4).unpair.1 && termTest boundNames (code / 4).unpair.2
  else (BaseTermPrograms.variablesCode (code / 4)).all (fun i => !boundNames.contains i)
termination_by code
decreasing_by
  all_goals
    have hp : 0 < code := by omega
    have hd := Nat.div_lt_self hp (by decide : 1 < 4)
    have hl := Nat.unpair_left_le (code / 4)
    have hr := Nat.unpair_right_le (code / 4)
    omega

def test (boundNames : List Nat) (code : Nat) : Bool :=
  if code % 5 = 0 ∨ code % 5 = 1 then termTest boundNames (code / 5).unpair.1 && termTest boundNames (code / 5).unpair.2
  else if code % 5 = 2 then test boundNames (code / 5)
  else if code % 5 = 3 then test boundNames (code / 5).unpair.1 && test boundNames (code / 5).unpair.2
  else test ((code / 5).unpair.1 :: boundNames) (code / 5).unpair.2
termination_by code
decreasing_by
  all_goals
    have hp : 0 < code := by omega
    have hd := Nat.div_lt_self hp (by decide : 1 < 5)
    have hl := Nat.unpair_left_le (code / 5)
    have hr := Nat.unpair_right_le (code / 5)
    omega

def freezeTerm (values : List Nat) (code : Nat) : Nat :=
  if code % 4 = 0 ∨ code % 4 = 1 then code
  else if code % 4 = 2 then 4 * Nat.pair (freezeTerm values (code / 4).unpair.1) (freezeTerm values (code / 4).unpair.2) + 2
  else 4 * value values code
termination_by code
decreasing_by
  all_goals
    have hp : 0 < code := by omega
    have hd := Nat.div_lt_self hp (by decide : 1 < 4)
    have hl := Nat.unpair_left_le (code / 4)
    have hr := Nat.unpair_right_le (code / 4)
    omega

def freezeFormula (values : List Nat) (code : Nat) : Nat :=
  if code % 5 = 0 ∨ code % 5 = 1 then
    5 * Nat.pair (freezeTerm values (code / 5).unpair.1) (freezeTerm values (code / 5).unpair.2) + code % 5
  else if code % 5 = 2 then 5 * freezeFormula values (code / 5) + 2
  else if code % 5 = 3 then
    5 * Nat.pair (freezeFormula values (code / 5).unpair.1) (freezeFormula values (code / 5).unpair.2) + 3
  else 5 * Nat.pair (code / 5).unpair.1 (freezeFormula values (code / 5).unpair.2) + 4
termination_by code
decreasing_by
  all_goals
    have hp : 0 < code := by omega
    have hd := Nat.div_lt_self hp (by decide : 1 < 5)
    have hl := Nat.unpair_left_le (code / 5)
    have hr := Nat.unpair_right_le (code / 5)
    omega

def decide (values : List Nat) (code : Nat) : Option Bool :=
  if test [] code then AdditiveParameterDecision.Code.decide values (freezeFormula values code) else none

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiPrograms.Code
