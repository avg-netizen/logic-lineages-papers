module
public import LogicLineages.OrdinalComparison.GuardChildMeasureCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.CanonicalGuardSelector
open PolynomialGraphCompletion OuterShiftNormalization CounterWordGuardCompletion
open CounterRangeWordGuardCompletion MixedRangeWordGuardCompletion GuardChildMeasureCompletion

/-- Only unused fields are discarded. Genuine mass, rank and coherent index
are preserved in every source evaluator. Malformed tags are left untouched. -/
def canonicalHead (a : Letter) : Letter :=
  if a.1 = 1 then phiLetter
  else if a.1 = 2 then quadraticLetter a.2.2.2
  else if a.1 = 3 then kernelLetter a.2.1 a.2.2.1 a.2.2.2
  else if a.1 = 4 then counterLetter a.2.1 a.2.2.1
  else a

def IsCanonical (a : Letter) : Prop := canonicalHead a = a

def viewPrefix (w : Word) : Word := (coreWord w).reverse.tail.reverse
def rawHead (w : Word) : Letter := ((coreWord w).reverse.head?).getD phiLetter
def viewHead (w : Word) : Letter := canonicalHead (rawHead w)

/-- The default head is ignored when the original word has no nonlinear head. -/
def preparedWord (w : Word) : Word :=
  if coreWord w = [] then [shiftLetter (outerShift w)]
  else viewPrefix w ++ [viewHead w,shiftLetter (outerShift w)]

/-- Case number, reversed orientation, and child in the original side order. -/
abbrev Choice := Nat × Bool × WordPair

/-- Total local selection. Its certified domain is admitted canonical nonzero
heads; malformed inputs still have a total, unclaimed output. -/
def selectHeads (A : Word) (a : Letter) (B : Word) (b : Letter) : Choice :=
  if a.1 = 4 then
    if b.1 = 4 then
      (1,false,(A++leaderWord (a.2.1-3) a.2.2.1,B++leaderWord (b.2.1-3) b.2.2.1))
    else (2,false,(A++leaderWord (a.2.1-3) a.2.2.1,rangeInputWord B b))
  else if b.1 = 4 then
    (2,true,(rangeInputWord A a,B++leaderWord (b.2.1-3) b.2.2.1))
  else if a.1 = 1 then (3,false,(A,rangeInputWord B b))
  else if b.1 = 1 then (3,true,(rangeInputWord A a,B))
  else if a.1 = 2 then
    if b.1 = 2 then (4,false,(A,B))
    else (7,true,(A,retainedWord B 0 (b.2.1-3) b.2.2.1))
  else if b.1 = 2 then (7,false,(retainedWord A 0 (a.2.1-3) a.2.2.1,B))
  else if a.2.1 = b.2.1 then (5,false,(A,B))
  else if b.2.1 < a.2.1 then
    (6,false,(retainedWord A (b.2.1-3+1) (a.2.1-b.2.1-1) a.2.2.1,B))
  else (6,true,(A,retainedWord B (a.2.1-3+1) (b.2.1-a.2.1-1) b.2.2.1))

/-- None means a terminal leaf case, not an unknown nonlinear case. -/
def selectWords (A B : Word) : Option Choice :=
  if coreWord A = [] ∨ coreWord B = [] then none
  else some (selectHeads (viewPrefix A) (viewHead A) (viewPrefix B) (viewHead B))

/-- A labeled certificate ties both returned case code and orientation to an
actual checked child constructor, rather than only bounding the numeric code. -/
inductive GuardCase (D : Nat) : Nat → Bool → WordPair → WordPair → Prop
  | counterCounter (A B : Word) (n m c e : Nat) (j k : Int)
      (hn : n+3 ≤ D) (hm : m+3 ≤ D) :
      GuardCase D 1 false (A++leaderWord n c,B++leaderWord m e)
        (A++[counterLetter (n+3) c,shiftLetter j],B++[counterLetter (m+3) e,shiftLetter k])
  | counterRange (A B : Word) (a : Letter) (n c : Nat) (j k : Int)
      (ha : LetterAllowed D a) (hr : RangeHead a) (hn : n+3 ≤ D) :
      GuardCase D 2 false (A++leaderWord n c,rangeInputWord B a)
        (A++[counterLetter (n+3) c,shiftLetter j],B++[a,shiftLetter k])
  | phiRange (A B : Word) (a : Letter) (j k : Int)
      (ha : LetterAllowed D a) (hr : RangeHead a) :
      GuardCase D 3 false (A,rangeInputWord B a)
        (A++[phiLetter,shiftLetter j],B++[a,shiftLetter k])
  | quadratic (A B : Word) (j k a b : Int) :
      GuardCase D 4 false (A,B)
        (A++[quadraticLetter j,shiftLetter a],B++[quadraticLetter k,shiftLetter b])
  | equalRank (A B : Word) (d c e : Nat) (j k a b : Int)
      (hd : 3 ≤ d) (hD : d ≤ D) :
      GuardCase D 5 false (A,B)
        (A++[kernelLetter d c j,shiftLetter a],B++[kernelLetter d e k,shiftLetter b])
  | mixedKernel (A B : Word) (n m c e : Nat) (j k a b : Int) (hD : n+m+4 ≤ D) :
      GuardCase D 6 false (retainedWord A (n+1) m c,B)
        (A++[kernelLetter (n+m+4) c j,shiftLetter a],B++[kernelLetter (n+3) e k,shiftLetter b])
  | mixedQuadratic (A B : Word) (m c : Nat) (j k a b : Int) (hD : m+3 ≤ D) :
      GuardCase D 7 false (retainedWord A 0 m c,B)
        (A++[kernelLetter (m+3) c j,shiftLetter a],B++[quadraticLetter k,shiftLetter b])
  | reverse {code : Nat} {next current : WordPair} (h : GuardCase D code false next current) :
      GuardCase D code true (next.2,next.1) (current.2,current.1)

end LogicLineages.OrdinalComparison.CanonicalGuardSelector
