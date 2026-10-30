module
public import LogicLineages.OrdinalComparison.PrefixTraceDefinitions
public import LogicLineages.OrdinalComparison.ActualTerminalDefinitions

@[expose] public section

namespace LogicLineages.OrdinalComparison

/-- Source input with prescribed total norm; source claims use t>=N(lambda). -/
noncomputable def actualHeadInitial (lam : Ordinal.{0}) (t : Nat) : Ordinal :=
  lam + ((t - actualOrdinalNorm lam : Nat) : Ordinal)

noncomputable def actualHeadValue (lam : Ordinal.{0}) (t : Nat) : Nat :=
  actualCollapse (actualHeadInitial lam t)

noncomputable def actualHeadEndpoint (lam : Ordinal.{0}) (t : Nat) : Nat :=
  actualTerminalValue (actualHeadInitial lam t)

noncomputable def actualHeadCount (lam : Ordinal.{0}) (t : Nat) : Nat :=
  actualReplacementCount (actualHeadInitial lam t)

end LogicLineages.OrdinalComparison
