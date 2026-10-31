module
public import LogicLineages.ModelsAlgebra.PGroups.TwoInfiniteTailSigmaDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
def twoInfiniteTailNoRawSigma : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x=0) → IsReducedAddGroup G →
    ∀ (γ : Ordinal.{0}) (N : ℕ) (a b : Fin N), a<b →
    (∀ x : (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G), p^N • x=0) →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p a.val :
      AddSubgroup (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G))) = Cardinal.aleph0 →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p b.val :
      AddSubgroup (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G))) = Cardinal.aleph0 →
    ∀ φ : Formula 0, Complexity .sigma (2*γ+3) φ →
      ¬ RawScottSentence (RawGroupStructure.ofGroup G) φ


def twoInfiniteTailNoSigma : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x=0) → IsReducedAddGroup G →
    ∀ (γ : Ordinal.{0}) (N : ℕ) (a b : Fin N), a<b →
    (∀ x : (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G), p^N • x=0) →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p a.val :
      AddSubgroup (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G))) = Cardinal.aleph0 →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p b.val :
      AddSubgroup (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G))) = Cardinal.aleph0 →
    ∀ φ : Formula 0, Complexity .sigma (2*γ+3) φ →
      ¬ GroupScottSentence G φ

end LogicLineages.ModelsAlgebra.PGroups.Targets
