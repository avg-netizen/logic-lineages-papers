module

public import LogicLineages.ModelsAlgebra.PGroups.UlmRankAssemblyTargets
public import LogicLineages.ModelsAlgebra.PGroups.FullShiftDefinitions

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def groupFiniteCyclicUlmRank : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (t : ℕ) (ℓ : Fin t → ℕ) (j : ℕ),
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j :
      AddSubgroup (∀ i : Fin t, ZMod (p ^ ℓ i)))) =
      ((Finset.univ.filter (fun i => j + 1 = ℓ i)).card : Cardinal)

def groupInfiniteCyclicUlmRank : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k j : ℕ),
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup (ℕ →₀ ZMod (p ^ k)))) =
      if j + 1 = k then Cardinal.aleph0 else 0

/-- The genuine invariant of the literal source normal form. No assertion
that arbitrary bounded groups possess this form or that invariants classify. -/
def groupFullShiftUlmRank : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k t : ℕ) (ℓ : Fin t → ℕ) (s : ℕ) (r : Fin s → ℕ) (j : ℕ),
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup (FullShiftGroup p k t ℓ s r))) =
      ((Finset.univ.filter (fun i => j + 1 = ℓ i)).card : Cardinal) +
      (if j + 1 = k then Cardinal.aleph0 else 0) +
      ((Finset.univ.filter (fun i => j + 1 = r i)).card : Cardinal)

end LogicLineages.ModelsAlgebra.PGroups.Targets
