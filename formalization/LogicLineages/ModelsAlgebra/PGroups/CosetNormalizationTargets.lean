module
public import LogicLineages.ModelsAlgebra.PGroups.FiltrationProfileTargets
public import Mathlib.Data.Finite.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupCosetProfileMaximum : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (B : AddSubgroup G) [Finite B] (x : G),
    ∃ b : B, ∀ c : B, ∀ α : Ordinal.{v},
      x + c ∈ (transfiniteFiltration p α : AddSubgroup G) →
      x + b ∈ (transfiniteFiltration p α : AddSubgroup G)

def groupCosetDoubleMaximum : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (B : AddSubgroup G) [Finite B] (x : G),
    ∃ b : B,
      (∀ c : B, ∀ α : Ordinal.{v}, x + c ∈ (transfiniteFiltration p α : AddSubgroup G) →
        x + b ∈ (transfiniteFiltration p α : AddSubgroup G)) ∧
      ∀ c : B,
        (∀ d : B, ∀ α : Ordinal.{v}, x + d ∈ (transfiniteFiltration p α : AddSubgroup G) →
          x + c ∈ (transfiniteFiltration p α : AddSubgroup G)) →
        ∀ α : Ordinal.{v}, p • (x + c) ∈ (transfiniteFiltration p α : AddSubgroup G) →
          p • (x + b) ∈ (transfiniteFiltration p α : AddSubgroup G)

end LogicLineages.ModelsAlgebra.PGroups.Targets
