module
public import LogicLineages.ModelsAlgebra.PGroups.OneInfiniteTailLowerDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
def oneInfiniteTailNoPi : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G]
    (γ : Ordinal.{0}) (k N : ℕ),
    (∀ x : G, ∃ j : ℕ, p^j • x=0) → IsReducedAddGroup G → 0<k → k≤N →
    (∀ x : (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G), p^N • x=0) →
    (Module.rank (ZMod p) (UlmLayer p (finiteFiltration p (k-1) :
      AddSubgroup (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G))) = Cardinal.aleph0) →
    (∀ j : ℕ, j<N → j≠k-1 → Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j :
      AddSubgroup (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G))) < Cardinal.aleph0) →
    (∃ j : ℕ, j<k-1 ∧ Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j :
      AddSubgroup (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G))) ≠ 0) →
    ∀ φ : Formula 0, Complexity .pi (2*γ+2) φ →
      ¬ RawScottSentence (RawGroupStructure.ofGroup G) φ
end LogicLineages.ModelsAlgebra.PGroups.Targets
