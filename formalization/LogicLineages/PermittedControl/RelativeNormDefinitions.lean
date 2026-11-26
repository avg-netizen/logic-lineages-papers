module
public import LogicLineages.OrdinalComparison.ActualOrdinalNormDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

/-- Literal restriction of the ordinary Cantor normal form to exponents ≥ e.
Reconstruction uses ordinary ordinal sum, not natural sum. -/
noncomputable def relativePrefix (mu e : Ordinal.{0}) : Ordinal :=
  ((Ordinal.CNF Ordinal.omega0 mu).filter (fun p => e ≤ p.1)).foldr
    (fun p r => Ordinal.omega0 ^ p.1 * p.2 + r) 0

/-- Source s_mu(e), before the separate zero-state convention. -/
noncomputable def relativeProfile (mu e : Ordinal.{0}) : Nat :=
  actualOrdinalNorm (relativePrefix mu e)

/-- At y=0 the full N(mu) is retained, as specified in entries.tex. -/
noncomputable def relativeCost (mu y : Ordinal.{0}) : Nat :=
  if y = 0 then actualOrdinalNorm mu
  else relativeProfile mu (Ordinal.log Ordinal.omega0 y)

end LogicLineages.PermittedControl
