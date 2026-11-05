module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainProgramsDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchPrograms.Code

def isPlain (code : Nat) : Bool := (LinearRows.Code.atoms code).all
  (fun a => PlainPhiDominance.Code.isPlain (LinearRows.Code.decodeAtom a).2.2)
def «variables» (code : Nat) : List Nat := (LinearRows.Code.atoms code).flatMap
  (fun a => (LinearRows.Code.decodeAtom a).2.2.2.map (fun b => b.2.2.1))
def cutoff (code : Nat) : Nat := ((LinearRows.Code.atoms code).map
  (fun a => MaximalPlainPrograms.Code.cutoff (LinearRows.Code.decodeAtom a))).sum

def lowerGuard (i c : Nat) : Nat :=
  ShiftedInputPrograms.Code.atom (-(c : Int), [(1, (0, i, 0, 0))])
def maximumGuard (i j : Nat) : Nat :=
  ShiftedInputPrograms.Code.atom (0, [(1, (0, i, 0, 0)), (-1, (0, j, 0, 0))])
def frame (i code : Nat) : Nat :=
  ShiftedInputPrograms.Code.conjunction (lowerGuard i (cutoff code))
    ((«variables» code).foldr (fun j rest =>
      ShiftedInputPrograms.Code.conjunction (maximumGuard i j) rest) 0)

/-- Replace atoms by formulas, preserving the literal radix-six Boolean spine. -/
def compile (i code : Nat) : Nat :=
  if code % 6 = 0 then 0 else if code % 6 = 1 then 1
  else if code % 6 = 2 then MaximalPlainPrograms.Code.compileAtom i (LinearRows.Code.decodeAtom (code / 6))
  else if code % 6 = 3 then 6 * compile i (code / 6) + 3
  else 6 * Nat.pair (compile i (code / 6).unpair.1)
    (compile i (code / 6).unpair.2) + code % 6
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 6 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 6)
    have hr := Nat.unpair_right_le (code / 6)
    omega

def framed (i code : Nat) : Nat := ShiftedInputPrograms.Code.conjunction (frame i code) (compile i code)
def eliminate (i code : Nat) : Nat := LinearRows.Code.eliminate i (framed i code)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchPrograms.Code
