module

public import LogicLineages.ModelsAlgebra.PGroups.CoordinateUlmTargets
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u

def groupProductFiniteUlm : Prop :=
  ∀ (G H : Type u) [AddCommGroup G] [AddCommGroup H] (p j : ℕ),
    Nonempty (UlmLayer p (finiteFiltration p j : AddSubgroup (G × H)) ≃ₗ[ZMod p]
      (UlmLayer p (finiteFiltration p j : AddSubgroup G) ×
       UlmLayer p (finiteFiltration p j : AddSubgroup H)))

def groupProductUlmRank : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G H : Type u) [AddCommGroup G] [AddCommGroup H] (j : ℕ),
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup (G × H))) =
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) +
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup H))

/-- Same-universe finite products; no rank-sum assertion for infinite Pi. -/
def groupPiUlmRank : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ι : Type u) [Finite ι] (G : ι → Type u)
    [∀ i, AddCommGroup (G i)] (j : ℕ),
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup (∀ i, G i))) =
      Cardinal.sum (fun i => Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup (G i))))

def groupFinsuppUlmRank : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ι G : Type u) [AddCommGroup G] (j : ℕ),
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup (ι →₀ G))) =
      Cardinal.mk ι * Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G))

end LogicLineages.ModelsAlgebra.PGroups.Targets
