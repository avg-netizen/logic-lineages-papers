module
public import LogicLineages.OrdinalComparison.ActualCollapseDefinitions

@[expose] public section

/-! Literal split and replacement of paper 05 `cor:closed-evaluation`.

Ordinal division has the orientation alpha = omega * (alpha / omega) + remainder.
Both multiplication and addition here are ordinary ordinal operations. The
finite remainder is converted through its cardinal. The replacement is the
independently defined actual maximum at the original state's control budget.
No encoded computability claim follows from these noncomputable definitions.
-/

namespace LogicLineages.OrdinalComparison

noncomputable def actualLimitPart (a : Ordinal.{0}) : Ordinal.{0} :=
  Ordinal.omega0 * (a / Ordinal.omega0)

noncomputable def actualTailPart (a : Ordinal.{0}) : Nat :=
  (a % Ordinal.omega0).card.toNat

noncomputable def actualDescentStep (a : Ordinal.{0}) : Ordinal.{0} :=
  actualMaximumPredecessor (actualLimitPart a) (Phi (actualOrdinalNorm a))

end LogicLineages.OrdinalComparison
