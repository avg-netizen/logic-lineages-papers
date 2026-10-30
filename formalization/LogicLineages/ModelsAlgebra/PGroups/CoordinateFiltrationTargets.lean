module

public import LogicLineages.ModelsAlgebra.PGroups.UlmDefinitions
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Algebra.Group.Pi.Lemmas

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

/-- Actual coordinate membership, including arbitrary dependent products. -/
def groupPiFiniteFiltration : Prop :=
  ∀ (ι : Type u) (G : ι → Type v) [∀ i, AddCommGroup (G i)]
    (p j : ℕ) (x : ∀ i, G i),
    x ∈ finiteFiltration p j ↔ ∀ i, x i ∈ finiteFiltration p j

def groupPiFiniteSocle : Prop :=
  ∀ (ι : Type u) (G : ι → Type v) [∀ i, AddCommGroup (G i)]
    (p j : ℕ) (x : ∀ i, G i),
    x ∈ pSocle p (finiteFiltration p j) ↔ ∀ i, x i ∈ pSocle p (finiteFiltration p j)

/-- Reverse membership requires a genuinely finite-support root, not a field. -/
def groupFinsuppFiniteFiltration : Prop :=
  ∀ (ι : Type u) (G : Type v) [AddCommGroup G] (p j : ℕ) (x : ι →₀ G),
    x ∈ finiteFiltration p j ↔ ∀ i, x i ∈ finiteFiltration p j

def groupFinsuppFiniteSocle : Prop :=
  ∀ (ι : Type u) (G : Type v) [AddCommGroup G] (p j : ℕ) (x : ι →₀ G),
    x ∈ pSocle p (finiteFiltration p j) ↔ ∀ i, x i ∈ pSocle p (finiteFiltration p j)

end LogicLineages.ModelsAlgebra.PGroups.Targets
