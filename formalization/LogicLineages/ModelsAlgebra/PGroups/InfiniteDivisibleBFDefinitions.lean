module
public import LogicLineages.ModelsAlgebra.PGroups.PrueferSocleDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.BackForthDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

/-- Literal existence of infinitely many independent copies of the genuine
Prüfer model. No divisible decomposition or comparison oracle is supplied. -/
def HasInfinitePrueferFamily (p : ℕ) (G : Type) [AddCommGroup G] : Prop :=
  ∃ e : DirectSum ℕ (fun _ => PrueferModel p) →+ G, Function.Injective e

def UlmRanksAgreeBelow (p : ℕ) (G H : Type) [AddCommGroup G] [AddCommGroup H]
    (δ : Ordinal.{0}) : Prop :=
  ∀ α < δ, Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) =
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H))

def UlmRanksLeInterval (p : ℕ) (G H : Type) [AddCommGroup G] [AddCommGroup H]
    (δ ε : Ordinal.{0}) : Prop :=
  ∀ α, δ ≤ α → α < ε →
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) ≤
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H))

def MapCutsExact {G H : Type} [AddCommGroup G] [AddCommGroup H] (p : ℕ)
    {B : AddSubgroup G} {C : AddSubgroup H} (f : B ≃+ C) (δ : Ordinal.{0}) : Prop :=
  ∀ b : B, ∀ β ≤ δ,
    (f b:H) ∈ transfiniteFiltration p β ↔ (b:G) ∈ transfiniteFiltration p β

def MapCutsForward {G H : Type} [AddCommGroup G] [AddCommGroup H] (p : ℕ)
    {B : AddSubgroup G} {C : AddSubgroup H} (f : B ≃+ C) (δ : Ordinal.{0}) : Prop :=
  ∀ b : B, ∀ β ≤ δ,
    (b:G) ∈ transfiniteFiltration p β → (f b:H) ∈ transfiniteFiltration p β

/-- The original group-language comparison on each tuple in the finite map.
The left structure is the target of f, matching the source's b↦a convention. -/
def SubgroupComparison {G H : Type} [AddCommGroup G] [AddCommGroup H]
    {B : AddSubgroup G} {C : AddSubgroup H} (f : B ≃+ C) (α : Ordinal.{0}) : Prop :=
  ∀ (n : ℕ) (b : Fin n → B),
    GroupBackAndForth.BackAndForth α (fun i => (f (b i):H)) (fun i => (b i:G))

end LogicLineages.ModelsAlgebra.PGroups
