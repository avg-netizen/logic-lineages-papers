module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainMaximumDefinitions
public import LogicLineages.OrdinalComparison.ControlResidueDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainMaximumResidue
open BlockRows PlainMaximum

/-- The existing actual constant-residue theorem, with the source atom's
positive modulus. This cutoff depends only on the literal atom, not on any
retained parameter valuation. -/
def cutoff (modulusMinusOne : Nat) : Nat := modulusMinusOne + 1 - 100

/-- Replace precisely the selected Phi(variable) contribution by its actual
computed residue. The signed constant terms remain tied to the same original
valuation; all other original occurrences survive literally. -/
def lowerRow (modulusMinusOne i : Nat) (r : Row) : Row :=
  ((.add r.1.1 (.multiply (headCoefficient i r).toNat
      (.numeral (fastControlResidue (modulusMinusOne + 1)))),
    .add r.1.2 (.multiply (-(headCoefficient i r)).toNat
      (.numeral (fastControlResidue (modulusMinusOne + 1))))),
    remainingOccurrences i r)
def lowerAtom (modulusMinusOne i : Nat) (r : Row) : Formula :=
  .atom (.divisible modulusMinusOne (lowerRow modulusMinusOne i r))

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainMaximumResidue
