module
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.ComparisonDefinitions
public import LogicLineages.OrdinalComparison.CanonicalGuardSelector.Definitions
public import LogicLineages.OrdinalComparison.CounterWordGuardCompletion.Definitions
public import LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion.Definitions
public import LogicLineages.OrdinalComparison.ShiftedPhiRangeWordGuardCompletion.Definitions
public import LogicLineages.OrdinalComparison.QuadraticWordGuardCompletion.Definitions
public import LogicLineages.OrdinalComparison.ShiftedEqualRankWordGuardCompletion.Definitions
public import LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.FullWordGuardCompletion
open PolynomialGraphCompletion WordGuardCompletion CanonicalGuardSelector
open OuterShiftNormalization

/-- The exact previously checked cutoff for a forward-oriented local case.
The seven case numbers are those returned by the literal canonical selector.
The default branch only makes the numeric program total. -/
def forwardTail (code : Nat) (A : Word) (a : Letter) (B : Word) (b : Letter)
    (j k : Int) : Nat :=
  if code = 1 then
    CounterWordGuardCompletion.guardTail A B (a.2.1-3) (b.2.1-3)
      a.2.2.1 b.2.2.1 j k
  else if code = 2 then
    CounterRangeWordGuardCompletion.guardTail A B (a.2.1-3) a.2.2.1 b j k
  else if code = 3 then
    ShiftedPhiRangeWordGuardCompletion.guardTail A B b j k
  else if code = 4 then
    QuadraticWordGuardCompletion.guardTail A B a.2.2.2 b.2.2.2 j k
  else if code = 5 then
    ShiftedEqualRankWordGuardCompletion.guardTail A B a.2.1 a.2.2.1 b.2.2.1
      a.2.2.2 b.2.2.2 j k
  else if code = 6 then
    MixedRangeWordGuardCompletion.kernelGuardTail A B (b.2.1-3)
      (a.2.1-b.2.1-1) a.2.2.1 b.2.2.1 a.2.2.2 b.2.2.2 j k
  else if code = 7 then
    MixedRangeWordGuardCompletion.quadraticGuardTail A B (a.2.1-3) a.2.2.1
      a.2.2.2 b.2.2.2 j k
  else 0

/-- A local case preserves either strict child order. Only its equality
branch is resolved by the original closed rank, mass and signed indices. -/
def forwardTie (code : Nat) (a b : Letter) (j k : Int) : Nat :=
  if code = 1 then
    lexOrder (orderNat (a.2.1-3) (b.2.1-3)) (orderInt j k)
  else if code = 2 then 0
  else if code = 3 then orderInt j k
  else if code = 4 then
    lexOrder (orderInt a.2.2.2 b.2.2.2) (orderInt j k)
  else if code = 5 ∨ code = 6 then
    lexOrder (orderNat b.2.2.1 a.2.2.1)
      (lexOrder (orderInt a.2.2.2 b.2.2.2) (orderInt j k))
  else if code = 7 then
    lexOrder (orderInt (a.2.2.2-(((a.2.2.1+1)/2 : Nat) : Int)) b.2.2.2)
      (orderInt j k)
  else 1

/-- Reversed cases use the same original local theorem with its arguments
exchanged. The recursive child itself remains in the original raw side order. -/
def headTail (A : Word) (a : Letter) (B : Word) (b : Letter) (j k : Int) : Nat :=
  let q := selectHeads A a B b
  if q.2.1 then forwardTail q.1 B b A a k j
  else forwardTail q.1 A a B b j k

/-- Selection's case number and orientation depend only on the two heads.
Reversal conjugates the comparison map and therefore reverses its tie value. -/
def headTie (a b : Letter) (j k : Int) : Nat :=
  let q := selectHeads [] a [] b
  if q.2.1 then reverseOrder (forwardTie q.1 b a k j)
  else forwardTie q.1 a b j k

/-- Original word domains are paid before the one-way outer-shift
normalization is used. All interior analytic thresholds use the existing
structural reach cutoffs inside forwardTail. -/
def dispatchTail (A B : Word) : Nat :=
  max (wordTail A) (max (wordTail B)
    (headTail (viewPrefix A) (viewHead A) (viewPrefix B) (viewHead B)
      (outerShift A) (outerShift B)))

def dispatchTie (A B : Word) : Nat :=
  headTie (viewHead A) (viewHead B) (outerShift A) (outerShift B)

end LogicLineages.OrdinalComparison.FullWordGuardCompletion
