module
public import LogicLineages.OrdinalComparison.SignedPhiSeparationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovUnarySign

/-- The ONE-variable part of Snyatkov p42display(1): a literal finite signed
row of shifted actual Phi values plus a signed linear remainder c*n+d.
Every original row occurrence, including zero/cancelled blocks, is retained. -/
abbrev Expression := SignedShiftCollection.Row × Int × Int

def value (E : Expression) (n : Nat) : Int :=
  SignedPhiSeparation.value E.1 n + E.2.1 * (n : Int) + E.2.2

def domainBound (E : Expression) : Nat := SignedShiftCollection.domainOffset E.1

/-- Concrete effective tail. For a surviving row, use its EXISTING exact
source delta, and explicitly dominate the entire linear remainder. -/
def threshold (E : Expression) : Nat :=
  if SignedShiftCollection.collected E.1 = [] then
    max (domainBound E) (E.2.2.natAbs + 1)
  else SignedPhiSeparation.delta E.1 +
    (E.2.1.natAbs + E.2.1.natAbs * SignedPhiSeparation.delta E.1 + E.2.2.natAbs + 1)

def tailSign (E : Expression) : Int :=
  if SignedShiftCollection.collected E.1 = [] then
    if E.2.1 = 0 then E.2.2.sign else E.2.1.sign
  else (SignedShiftCollection.leadingCoefficient E.1).sign

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovUnarySign
