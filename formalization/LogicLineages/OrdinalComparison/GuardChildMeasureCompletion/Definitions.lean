module
public import LogicLineages.OrdinalComparison.ComparisonMeasureDefinitions
public import LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.Definitions
public import LogicLineages.OrdinalComparison.OuterShiftNormalization.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.GuardChildMeasureCompletion
open PolynomialGraphCompletion CounterWordGuardCompletion CounterRangeWordGuardCompletion
open AdjacentRangeWordGuardCompletion MixedRangeWordGuardCompletion

abbrev WordPair := Word × Word

/-- Phi and V are admitted even when the parameter D is smaller than two. -/
def rankBound (D : Nat) : Nat := max 2 D

def counterCount (p : WordPair) : Nat := counterNodes p.1+counterNodes p.2
def rangeCount (r : Nat) (p : WordPair) : Nat := rangeNodes r p.1+rangeNodes r p.2

/-- The existing finite reverse-rank histogram type, populated by actual word
occurrences in increasing source-rank order. No semantic mass is discarded. -/
def rangeHistogram : (n : Nat) → Nat → WordPair → ComparisonKernelHistogram n
  | 0, _, _ => PUnit.unit
  | n+1, first, p => (rangeCount first p,rangeHistogram n (first+1) p)

def wordMeasure (D : Nat) (p : WordPair) : Nat × ComparisonKernelHistogram (rankBound D) :=
  (counterCount p,rangeHistogram (rankBound D) 1 p)

def ChildDecrease (D : Nat) (next current : WordPair) : Prop :=
  Prod.Lex Nat.lt (ComparisonKernelHistogramLt (rankBound D))
    (wordMeasure D next) (wordMeasure D current)

/-- These are the literal child word constructors from the independently
checked local guard cases. There is no assumed decrease or semantic oracle.
This enumerated relation is not a completed recursive guard compiler. -/
inductive GuardChild (D : Nat) : WordPair → WordPair → Prop
  | counterCounter (A B : Word) (n m c e : Nat) (j k : Int)
      (hn : n+3 ≤ D) (hm : m+3 ≤ D) :
      GuardChild D (A++leaderWord n c,B++leaderWord m e)
        (A++[counterLetter (n+3) c,shiftLetter j],B++[counterLetter (m+3) e,shiftLetter k])
  | counterRange (A B : Word) (a : Letter) (n c : Nat) (j k : Int)
      (ha : LetterAllowed D a) (hr : RangeHead a) (hn : n+3 ≤ D) :
      GuardChild D (A++leaderWord n c,rangeInputWord B a)
        (A++[counterLetter (n+3) c,shiftLetter j],B++[a,shiftLetter k])
  | phiRange (A B : Word) (a : Letter) (j k : Int)
      (ha : LetterAllowed D a) (hr : RangeHead a) :
      GuardChild D (A,rangeInputWord B a)
        (A++[phiLetter,shiftLetter j],B++[a,shiftLetter k])
  | quadratic (A B : Word) (j k a b : Int) :
      GuardChild D (A,B)
        (A++[quadraticLetter j,shiftLetter a],B++[quadraticLetter k,shiftLetter b])
  | equalRank (A B : Word) (d c e : Nat) (j k a b : Int)
      (hd : 3 ≤ d) (hD : d ≤ D) :
      GuardChild D (A,B)
        (A++[kernelLetter d c j,shiftLetter a],B++[kernelLetter d e k,shiftLetter b])
  | mixedKernel (A B : Word) (n m c e : Nat) (j k a b : Int) (hD : n+m+4 ≤ D) :
      GuardChild D (retainedWord A (n+1) m c,B)
        (A++[kernelLetter (n+m+4) c j,shiftLetter a],B++[kernelLetter (n+3) e k,shiftLetter b])
  | mixedQuadratic (A B : Word) (m c : Nat) (j k a b : Int) (hD : m+3 ≤ D) :
      GuardChild D (retainedWord A 0 m c,B)
        (A++[kernelLetter (m+3) c j,shiftLetter a],B++[quadraticLetter k,shiftLetter b])
  | swap {next current : WordPair} (h : GuardChild D next current) :
      GuardChild D (next.2,next.1) (current.2,current.1)

end LogicLineages.OrdinalComparison.GuardChildMeasureCompletion
