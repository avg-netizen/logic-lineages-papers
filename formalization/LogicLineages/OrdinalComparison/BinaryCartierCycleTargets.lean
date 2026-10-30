module
public import LogicLineages.OrdinalComparison.BinaryCartierCycleDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Actual F2 source eventual-cycle existence, as a finite numerator argument.
This does not claim periodicity for arbitrary perfect-field coefficients. -/
def ActualBinaryProperNumeratorFinite : Prop :=
  ∀ d : Nat, Finite (ActualBinaryProperNumerator d)

def ActualBinaryCartierNumeratorIteration : Prop :=
  ∀ (d : Nat) (U : ActualBinaryProperNumerator d) (j : Nat),
    (actualDifferentialCartier^[j]) (actualBinaryRationalDifferential d U.val) =
      actualBinaryRationalDifferential d ((actualBinaryProperNumeratorStep d)^[j] U).val

def ActualBinaryCartierEventualCycle : Prop :=
  ∀ (d : Nat) (U : ActualBinaryProperNumerator d), ∃ j p : Nat, 0 < p ∧
    ∀ k : Nat,
      (actualDifferentialCartier^[j + k + p]) (actualBinaryRationalDifferential d U.val) =
        (actualDifferentialCartier^[j + k]) (actualBinaryRationalDifferential d U.val)

end LogicLineages.OrdinalComparison.Targets
