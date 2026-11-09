module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.DominantBoundary

/-- The first positive argument at which the scaled Phi value crosses a
threshold. The exceptional argument zero is retained separately by the exact
boundary target. This is the existing original floor inverse, not a search
over assignments or a supplied projection function. -/
def positiveCrossing (a target : Nat) : Nat :=
  SnyatkovInverse.phiInverse ((target - 1) / a) + 1

def center (a : Nat) (lower : Term) : Term :=
  .add (.phiInverse (.divide a (.subtract (.multiply 2 lower) (.numeral 1)))) (.numeral 1)

/-- A uniform five-element band. Truncated subtraction at centers 1 and 2
only adds candidates; every original constraint is retained in the output. -/
def argumentCandidate (a : Nat) (lower : Term) (d : Nat) : Term :=
  .add (.subtract (center a lower) (.numeral 2)) (.numeral d)

def replacement (a : Nat) (lower : Term) (shift : Int) (d : Nat) : Term :=
  shiftTerm (argumentCandidate a lower d) (-shift)

/-- The concrete failure of a wide dominant interval at the inverse boundary.
Twice the upper endpoint is smaller than three times the next scaled Phi. -/
def noWide (a : Nat) (lower upper : Term) : Matrix :=
  .less (.multiply 2 upper)
    (.multiply (3 * a) (.phi (.add (center a lower) (.numeral 1))))

/-- Necessary endpoint bounds for a source row lying between lower and upper
and between one half and three halves of its dominant scaled Phi summand.
The original signed-argument domain and the no-wide condition are explicit. -/
def region (i a : Nat) (shift : Int) (lower upper : Term) : Matrix :=
  .conjunction (shiftDomain (.variable i) shift)
    (.conjunction (noWide a lower upper)
      (.conjunction
        (atMost (.multiply 2 lower)
          (.multiply (3 * a) (.phi (shiftTerm (.variable i) shift))))
        (atMost (.multiply a (.phi (shiftTerm (.variable i) shift)))
          (.multiply 2 upper))))

/-- Actual parameter-preserving nonlinear projection for this source
dominant-boundary case. All other original constraints, Boolean positions and
correlations are copied literally into every substituted branch. -/
def project (i a : Nat) (shift : Int) (lower upper : Term) (p : Matrix) : Matrix :=
  Matrix.any ((List.range 5).map (fun d =>
    (Matrix.conjunction (region i a shift lower upper) p).substitute i
      (replacement a lower shift d)))

namespace Code
def divide (c x : Nat) : Nat := 10 * Nat.pair c x + 5
def inverse (x : Nat) : Nat := 10 * x + 8
def center (a lower : Nat) : Nat :=
  WindowCode.add
    (inverse (divide a (WindowCode.subtract (WindowCode.multiply 2 lower) (WindowCode.numeral 1))))
    (WindowCode.numeral 1)
def argumentCandidate (a lower d : Nat) : Nat :=
  WindowCode.add (WindowCode.subtract (center a lower) (WindowCode.numeral 2))
    (WindowCode.numeral d)
def replacement (a lower : Nat) (shift : Int) (d : Nat) : Nat :=
  WindowCode.shift (argumentCandidate a lower d) (-shift)
def noWide (a lower upper : Nat) : Nat :=
  WindowCode.less (WindowCode.multiply 2 upper)
    (WindowCode.multiply (3 * a)
      (WindowCode.phi (WindowCode.add (center a lower) (WindowCode.numeral 1))))
def region (i a : Nat) (shift : Int) (lower upper : Nat) : Nat :=
  WindowCode.conjunction (WindowCode.domain (WindowCode.var i) shift)
    (WindowCode.conjunction (noWide a lower upper)
      (WindowCode.conjunction
        (WindowCode.atMost (WindowCode.multiply 2 lower)
          (WindowCode.multiply (3 * a) (WindowCode.phi (WindowCode.shift (WindowCode.var i) shift))))
        (WindowCode.atMost (WindowCode.multiply a (WindowCode.phi (WindowCode.shift (WindowCode.var i) shift)))
          (WindowCode.multiply 2 upper))))

abbrev Input := Nat × (Nat × (Int × (Nat × (Nat × Nat))))
def project (q : Input) : Nat :=
  WindowCode.any ((List.range 5).map (fun d =>
    WindowCode.matrixSubstitute q.1 (replacement q.2.1 q.2.2.2.1 q.2.2.1 d)
      (WindowCode.conjunction
        (region q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1) q.2.2.2.2.2)))
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.DominantBoundary
