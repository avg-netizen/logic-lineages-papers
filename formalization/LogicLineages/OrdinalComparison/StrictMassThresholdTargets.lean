module
public import LogicLineages.OrdinalComparison.StrictMassThresholdDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- Exact displayed limit threshold, not a larger replacement. -/
def ActualStrictMassLimitThreshold : Prop :=
  ∀ eta : NONote, Order.IsSuccLimit eta.1.repr →
    actualStrictMassThreshold eta=max 7 (actualOrdinalNorm (Ordinal.omega0^eta.1.repr)+1)

/-- Exact displayed recursive successor threshold (7.6). The predecessor is
faithfully represented and its base at exponent two is tested syntactically
by the executable algorithm, with actual ordinal equality calibrated here. -/
def ActualStrictMassSuccessorThreshold : Prop :=
  ∀ eta pred : NONote, eta.1.repr=pred.1.repr+1 → (2 : Ordinal) ≤ pred.1.repr →
    actualStrictMassThreshold eta =
      max 4 (max (actualOrdinalNorm (Ordinal.omega0^eta.1.repr))
        (max (2*actualOrdinalNorm (Ordinal.omega0^pred.1.repr))
          (max (max 8 (actualOrdinalNorm (Ordinal.omega0^pred.1.repr)))
            (if pred.1.repr=(2 : Ordinal) then 0 else actualStrictMassThreshold pred))))

end LogicLineages.OrdinalComparison.Targets
