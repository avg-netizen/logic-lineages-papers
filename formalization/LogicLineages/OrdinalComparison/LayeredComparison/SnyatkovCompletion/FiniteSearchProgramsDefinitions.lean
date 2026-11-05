module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchSourceDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchPrograms.Code

def test (code : Nat) : Bool :=
  ScopedPhiPrograms.Code.test [] code ||
    if code % 5 = 0 ∨ code % 5 = 1 then false
    else if code % 5 = 2 then test (code / 5)
    else if code % 5 = 3 then test (code / 5).unpair.1 && test (code / 5).unpair.2
    else (BoundedSourcePrograms.Code.guard (code / 5).unpair.1 (code / 5).unpair.2).isSome && test (code / 5).unpair.2
termination_by code
decreasing_by
  all_goals
    have hp : 0 < code := by omega
    have hd := Nat.div_lt_self hp (by decide : 1 < 5)
    have hl := Nat.unpair_left_le (code / 5)
    have hr := Nat.unpair_right_le (code / 5)
    omega

def answer (values : List Nat) (code : Nat) : Bool :=
  if ScopedPhiPrograms.Code.test [] code then (ScopedPhiPrograms.Code.decide values code).getD false
  else if code % 5 = 0 ∨ code % 5 = 1 then false
  else if code % 5 = 2 then !answer values (code / 5)
  else if code % 5 = 3 then answer values (code / 5).unpair.1 && answer values (code / 5).unpair.2
  else match BoundedSourcePrograms.Code.guard (code / 5).unpair.1 (code / 5).unpair.2 with
    | none => false
    | some t => (List.range (ScopedPhiPrograms.Code.value values t)).any (fun n =>
        answer (BoundedSourcePrograms.Code.update values (code / 5).unpair.1 n) (code / 5).unpair.2)
termination_by code
decreasing_by
  all_goals
    have hp : 0 < code := by omega
    have hd := Nat.div_lt_self hp (by decide : 1 < 5)
    have hl := Nat.unpair_left_le (code / 5)
    have hr := Nat.unpair_right_le (code / 5)
    omega

def decide (values : List Nat) (code : Nat) : Option Bool :=
  if test code then some (answer values code) else none

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchPrograms.Code
