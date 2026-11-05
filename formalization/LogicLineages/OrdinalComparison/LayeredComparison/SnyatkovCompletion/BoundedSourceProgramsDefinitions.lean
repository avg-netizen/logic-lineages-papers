module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourcePrograms.Code

/-- Exact finite representation of an original name update, with zero defaults. -/
def update (values : List Nat) (i n : Nat) : List Nat :=
  (List.range (max values.length (i + 1))).map (fun j => if j = i then n else values.getD j 0)

/-- Parse the literal source conjunct, less-than atom and operand operand,
then check actual support of the proposed bound. -/
def guard (i code : Nat) : Option Nat :=
  let atom := (code / 5).unpair.1
  let operand := (atom / 5).unpair.1
  let bound := (atom / 5).unpair.2
  if code % 5 = 3 ∧ atom % 5 = 1 ∧ operand % 4 = 1 ∧ operand / 4 = i ∧
      i ∉ BaseTermPrograms.variablesCode bound then some bound else none

def test (code : Nat) : Bool :=
  if code % 5 = 0 ∨ code % 5 = 1 then true
  else if code % 5 = 2 then test (code / 5)
  else if code % 5 = 3 then test (code / 5).unpair.1 && test (code / 5).unpair.2
  else (guard (code / 5).unpair.1 (code / 5).unpair.2).isSome && test (code / 5).unpair.2
termination_by code
decreasing_by
  all_goals
    have hp : 0 < code := by omega
    have hd := Nat.div_lt_self hp (by decide : 1 < 5)
    have hl := Nat.unpair_left_le (code / 5)
    have hr := Nat.unpair_right_le (code / 5)
    omega

def answer (values : List Nat) (code : Nat) : Bool :=
  if code % 5 = 0 then decide (ScopedPhiPrograms.Code.value values (code / 5).unpair.1 =
    ScopedPhiPrograms.Code.value values (code / 5).unpair.2)
  else if code % 5 = 1 then decide (ScopedPhiPrograms.Code.value values (code / 5).unpair.1 <
    ScopedPhiPrograms.Code.value values (code / 5).unpair.2)
  else if code % 5 = 2 then !answer values (code / 5)
  else if code % 5 = 3 then answer values (code / 5).unpair.1 && answer values (code / 5).unpair.2
  else match guard (code / 5).unpair.1 (code / 5).unpair.2 with
    | none => false
    | some t => (List.range (ScopedPhiPrograms.Code.value values t)).any (fun n =>
        answer (update values (code / 5).unpair.1 n) (code / 5).unpair.2)
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

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourcePrograms.Code
