module
public import LogicLineages.OrdinalComparison.OuterShiftNormalization.Definitions
public import LogicLineages.OrdinalComparison.CounterWordGuardCompletion.Definitions
public import LogicLineages.OrdinalComparison.ComparisonMeasureDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion
open PolynomialGraphCompletion WordGuardCompletion OuterShiftNormalization
open CounterWordGuardCompletion

/-- The original word row is retained literally. Outer shifts are moved into
the integer constant; their original individual domains remain hypotheses. -/
def normalizeRow (r : Row) : Row :=
  (r.1 + (r.2.map (fun a => a.1 * outerShift a.2.2)).sum,
    r.2.map (fun a => (a.1,a.2.1,coreWord a.2.2)))

/-- The residual source words in the descending entry order of the actual
counter expansion. The rank is the actual final counter head, not a rank
attached to the interior word or its raw variable. -/
def residualWords : Nat → Nat → List (Nat × Word)
  | 0, c => [(3,[counterLetter 3 (c+3)])]
  | n+1, c =>
      (n+4,[counterLetter (n+4) (c+n+4)]) ::
        (residualWords n c).map (fun p =>
          (p.1,kernelLetter (n+4) (c+n+4) 0 :: p.2))

def counterWord (A : Word) (n c : Nat) : Word :=
  A ++ [counterLetter (n+3) c]

def leaderValueWord (A : Word) (n c : Nat) : Word :=
  A ++ leaderWord n c ++ [phiLetter]

/-- Doubling keeps the literal half-leader identity in integer arithmetic.
All generated terms retain the original raw name and actual interior A. -/
def counterExpansionRow (a : Int) (i : Nat) (A : Word) (n c : Nat) : Row :=
  (2*a*(1-(((c+1)/2 : Nat) : Int)),
    (a,i,leaderValueWord A n c) ::
      (residualWords n c).map (fun p => (2*a,i,A++p.2)))

def expansionWords (A : Word) (n c : Nat) : List Word :=
  counterWord A n c :: leaderValueWord A n c ::
    (residualWords n c).map (fun p => A++p.2)

/-- Every original and generated word pays its own composed domain tail;
the source-process bridge is paid at the actual reached input of A. -/
def expansionTail (A : Word) (n c : Nat) : Nat :=
  max (reachTail A (leaderTail n c))
    (((expansionWords A n c).map wordTail).foldr max 0)

/-- Only current literal occurrences can supply nonlinear growth provenance.
A removed occurrence leaves no label behind on a different residual. -/
def CurrentNonlinear (i : Nat) (r : Row) : Prop :=
  ∃ a ∈ r.2, a.1 ≠ 0 ∧ a.2.1 = i ∧ coreWord a.2.2 ≠ []

/-- Top-level row ranks count one surviving ordinary range atom at rank zero,
or its final counter rank. Nested argument nodes are deliberately absent. -/
def topRank (w : Word) : Nat :=
  if (w.getLastD phiLetter).1 = 4 then (w.getLastD phiLetter).2.1 else 0

def rowRankList (r : Row) : List Nat :=
  (r.2.filter (fun a => a.1 != 0 && coreWord a.2.2 != [])).map
    (fun a => topRank (coreWord a.2.2))

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion
