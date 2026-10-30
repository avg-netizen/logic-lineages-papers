module

public import LogicLineages.ModelsAlgebra.PGroups.UlmDefinitions
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

/-- Literal cyclic exponent bound, including p=0 and k=0. -/
def groupCyclicFiltrationBottom : Prop :=
  ∀ (p k j : ℕ), k ≤ j →
    (finiteFiltration p j : AddSubgroup (ZMod (p ^ k))) = ⊥

/-- Below its actual length a cyclic p-group has its full socle; no
quotient dimension or decomposition correctness is assumed. -/
def groupCyclicFiltrationSocle : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k j : ℕ), j < k →
    pSocle p (finiteFiltration p j : AddSubgroup (ZMod (p ^ k))) = pSocle p ⊤

end LogicLineages.ModelsAlgebra.PGroups.Targets
