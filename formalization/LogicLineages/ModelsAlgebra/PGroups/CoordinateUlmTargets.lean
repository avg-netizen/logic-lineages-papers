module

public import LogicLineages.ModelsAlgebra.PGroups.CoordinateFiltrationTargets
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.Algebra.Module.Pi

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

/-- Actual quotient/module equivalence, not an equality of an assigned invariant.
No dimension sum is asserted for an infinite product. -/
def groupPiFiniteUlm : Prop :=
  ∀ (ι : Type u) (G : ι → Type v) [∀ i, AddCommGroup (G i)] (p j : ℕ),
    Nonempty (UlmLayer p (finiteFiltration p j : AddSubgroup (∀ i, G i)) ≃ₗ[ZMod p]
      (∀ i, UlmLayer p (finiteFiltration p j : AddSubgroup (G i))))

/-- Surjectivity must be paid by a zero-preserving finite-support choice of
actual quotient representatives. -/
def groupFinsuppFiniteUlm : Prop :=
  ∀ (ι : Type u) (G : Type v) [AddCommGroup G] (p j : ℕ),
    Nonempty (UlmLayer p (finiteFiltration p j : AddSubgroup (ι →₀ G)) ≃ₗ[ZMod p]
      (ι →₀ UlmLayer p (finiteFiltration p j : AddSubgroup G)))

end LogicLineages.ModelsAlgebra.PGroups.Targets
