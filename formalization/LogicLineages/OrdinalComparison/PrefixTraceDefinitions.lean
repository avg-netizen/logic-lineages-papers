module
public import LogicLineages.OrdinalComparison.CompatiblePrefixDefinitions

@[expose] public section

namespace LogicLineages.OrdinalComparison

/-- Literal iterates, used only through the first finite remainder count. -/
noncomputable def actualControlledStateAfter (g : Nat → Nat) (a : Ordinal.{0}) (k : Nat) : Ordinal :=
  ((actualControlledStep g)^[k]) a

/-- Exact residual budget above a prefix of norm c. -/
def prefixRemainderControl (h : Nat → Nat) (c n : Nat) : Nat := h (c + n) - c

end LogicLineages.OrdinalComparison
