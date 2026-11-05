module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodecDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BooleanSourceBlocks

/-- Boolean closure of the existing literal homogeneous-prefix fragment.
An existential binder is never recursively crossed after its homogeneous test
fails; this prevents a Boolean wrapper from admitting mixed alternation. -/
def admissible (p : SourceFormula) : Bool :=
  HomogeneousSource.admissible p ||
    match p with
    | .negative q => admissible q
    | .conjunction q r => admissible q && admissible r
    | _ => false

def combine (a b : Option Bool) : Option Bool :=
  a.bind (fun x => b.map (fun y => x && y))

def decide (values : List Nat) (p : SourceFormula) : Option Bool :=
  if HomogeneousSource.admissible p then HomogeneousSource.decide values p
  else match p with
    | .negative q => (decide values q).map Bool.not
    | .conjunction q r => combine (decide values q) (decide values r)
    | _ => none

namespace Code
/-- Concrete recursion on the original bijective source code. Existing block
answers are used only when the existing literal block recognizer accepts. -/
def decide (values : List Nat) (code : Nat) : Option Bool :=
  if HomogeneousSource.Code.admissible code then HomogeneousSource.Code.decide values code
  else if code % 5 = 2 then (decide values (code / 5)).map Bool.not
  else if code % 5 = 3 then combine (decide values (code / 5).unpair.1)
    (decide values (code / 5).unpair.2)
  else none
termination_by code
decreasing_by
  all_goals
    have hp : 0 < code := by omega
    have hd := Nat.div_lt_self hp (by decide : 1 < 5)
    have hl := Nat.unpair_left_le (code / 5)
    have hr := Nat.unpair_right_le (code / 5)
    omega
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BooleanSourceBlocks
