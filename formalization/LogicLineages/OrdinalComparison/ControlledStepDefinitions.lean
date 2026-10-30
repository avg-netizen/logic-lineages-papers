module
public import LogicLineages.OrdinalComparison.ActualDescentDefinitions

@[expose] public section

namespace LogicLineages.OrdinalComparison

/-- The literal source descent step for an arbitrary norm control. Only its
nonfinite source domain is assigned meaning; count evaluation stops at finite inputs. -/
noncomputable def actualControlledStep (g : Nat → Nat) (a : Ordinal.{0}) : Ordinal :=
  actualMaximumPredecessor (actualLimitPart a) (g (actualOrdinalNorm a))

end LogicLineages.OrdinalComparison
