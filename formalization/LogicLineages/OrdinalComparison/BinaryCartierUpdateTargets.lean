module
public import LogicLineages.OrdinalComparison.BinaryPoleRemovalDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Genuine source F2 rational Cartier update, connecting the differential
state to the already calibrated finite odd-digit polynomial transition.
This is equality of complete rational states, not one scalar observation. -/
def ActualBinaryRationalCartierUpdate : Prop :=
  ∀ d : Nat, ∀ U : Polynomial (ZMod 2),
    actualDifferentialCartier (actualBinaryRationalDifferential d U) =
      actualBinaryRationalDifferential d
        (actualBinaryPolynomialDigit true (U * actualBinarySourceDenominator d))

end LogicLineages.OrdinalComparison.Targets
