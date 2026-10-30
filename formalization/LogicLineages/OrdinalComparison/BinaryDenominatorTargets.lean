module
public import LogicLineages.OrdinalComparison.BinaryDenominatorDefinitions

@[expose] public section

/-! Exact literal denominator suppliers for paper10, paper.tex392–417.
These do not identify any restricted-partition generating coefficient. -/

namespace LogicLineages.OrdinalComparison.Targets

def ActualBinarySourceDenominatorConstant : Prop :=
  ∀ d : Nat, (actualBinarySourceDenominator d).coeff 0 = 1

def ActualBinarySourceDenominatorDegree : Prop :=
  ∀ d : Nat, (actualBinarySourceDenominator d).degree =
    (actualBinarySourceDimension d : WithBot Nat)

def ActualBinarySourceDimensionPositive : Prop :=
  ∀ d : Nat, 0 < d → 0 < actualBinarySourceDimension d

end LogicLineages.OrdinalComparison.Targets
