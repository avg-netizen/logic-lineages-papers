module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainRowsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranch
open NormalForm

def isPlain (p : Formula) : Bool :=
  (LinearRows.atoms p).all (fun a => PlainPhiDominance.isPlain a.row)
/-- One effective bound dominates every original atomic cutoff. -/
def cutoff (p : Formula) : Nat := ((LinearRows.atoms p).map MaximalPlainRows.cutoff).sum

def lowerGuard (i c : Nat) : Formula :=
  .atom (.nonnegative (-(c : Int), [(1, .variable i)]))
def maximumGuard (i j : Nat) : Formula :=
  .atom (.nonnegative (0, [(1, .variable i), (-1, .variable j)]))
def frame (i : Nat) (p : Formula) : Formula :=
  .conjunction (lowerGuard i (cutoff p))
    (p.variables.foldr (fun j rest => .conjunction (maximumGuard i j) rest) .truth)

/-- Preserve every Boolean constructor at its original position. In particular,
source domain formulas already in the input are neither moved nor discarded. -/
def compile (i : Nat) : Formula → Formula
  | .truth => .truth
  | .falsity => .falsity
  | .atom a => MaximalPlainRows.compileAtom i a
  | .negative p => .negative (compile i p)
  | .conjunction p q => .conjunction (compile i p) (compile i q)
  | .disjunction p q => .disjunction (compile i p) (compile i q)
def framed (i : Nat) (p : Formula) : Formula := .conjunction (frame i p) (compile i p)
def eliminate (i : Nat) (p : Formula) : Formula := LinearRows.eliminate i (framed i p)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranch
