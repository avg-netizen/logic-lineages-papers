module
public import LogicLineages.OrdinalComparison.BinaryPartitionSeriesDefinitions

@[expose] public section

/-! Source paper10 eq:partition-series (paper.tex195–204), reduced over F2 for
thm:observer (419–433). No claim of the full integer generating-series identity
is made. All coefficients are the actual previously defined partition counts. -/

namespace LogicLineages.OrdinalComparison.Targets

def ActualBinaryPartitionSeriesBase : Prop := actualBinaryPartitionSeries 0 = 1

def ActualBinaryPartitionSeriesFactor : Prop :=
  ∀ d : Nat,
    (1 + PowerSeries.X ^ (d + 1)) * actualBinaryPartitionSeries (d + 1) =
      actualBinaryPartitionSeries d

def ActualBinaryPartitionSeriesProduct : Prop :=
  ∀ d : Nat, (actualBinarySourceDenominator d : PowerSeries (ZMod 2)) *
    actualBinaryPartitionSeries d = 1

def ActualBinaryPartitionSeriesQuotient : Prop :=
  ∀ d : Nat, actualBinaryPartitionSeries d =
    actualPolynomialSeriesQuotient (actualBinarySourceDenominator d) 1

end LogicLineages.OrdinalComparison.Targets
