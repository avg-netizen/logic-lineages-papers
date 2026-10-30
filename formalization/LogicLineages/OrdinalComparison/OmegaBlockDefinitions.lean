module
public import LogicLineages.OrdinalComparison.HeadEndpointDefinitions
public import LogicLineages.OrdinalComparison.CompatiblePrefixDefinitions

@[expose] public section

namespace LogicLineages.OrdinalComparison

/-- Literal compensated source segment which deletes one omega^omega copy
with retained numerical mass c and prescribed original total norm u. -/
noncomputable def actualOmegaCopyCount (c u : Nat) : Nat :=
  actualControlledCount (compensatedPrefixControl c)
    (actualHeadInitial (Ordinal.omega0 ^ Ordinal.omega0) (u - c))

noncomputable def actualOmegaCopyState (c u i : Nat) : Ordinal.{0} :=
  actualControlledStateAfter (compensatedPrefixControl c)
    (actualHeadInitial (Ordinal.omega0 ^ Ordinal.omega0) (u - c)) i

end LogicLineages.OrdinalComparison
