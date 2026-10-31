module
public import LogicLineages.ModelsAlgebra.PGroups.OneInfiniteTailDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def oneInfiniteTailPiUpper : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G]
    (γ : Ordinal.{0}) [Countable γ.ToType] (k N : ℕ),
    (∀ x : G, ∃ j : ℕ, p^j • x=0) → 0<k → k≤N →
    (∀ x : (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G), p^N • x=0) →
    (Module.rank (ZMod p) (UlmLayer p (finiteFiltration p (k-1) :
      AddSubgroup (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G))) = Cardinal.aleph0) →
    (∀ j : ℕ, j<N → j≠k-1 → Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j :
      AddSubgroup (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G))) < Cardinal.aleph0) →
    (∀ j : ℕ, j<k-1 → Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j :
      AddSubgroup (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G))) = 0) →
    ∃ φ : Formula 0, Complexity .pi (2*γ+2) φ ∧ RawScottSentence (RawGroupStructure.ofGroup G) φ

def oneInfiniteTailDifferenceUpper : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G]
    (γ : Ordinal.{0}) [Countable γ.ToType] (k N : ℕ),
    (∀ x : G, ∃ j : ℕ, p^j • x=0) → 0<k → k≤N →
    (∀ x : (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G), p^N • x=0) →
    (Module.rank (ZMod p) (UlmLayer p (finiteFiltration p (k-1) :
      AddSubgroup (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G))) = Cardinal.aleph0) →
    (∀ j : ℕ, j<N → j≠k-1 → Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j :
      AddSubgroup (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G))) < Cardinal.aleph0) →
    ∃ d : DifferenceFormula 0, d.AtLevel (2*γ+2) ∧
      RawDifferenceScottSentence (RawGroupStructure.ofGroup G) d
end LogicLineages.ModelsAlgebra.PGroups.Targets
