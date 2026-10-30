module
public import LogicLineages.ModelsAlgebra.PGroups.RelativizedDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.QuotientFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u v

def groupTerminalSigmaOneTransfer : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (δ : Ordinal.{v}) (A K T : AddSubgroup G),
    (transfiniteFiltration p δ : AddSubgroup G) = K ⊔ T → Disjoint K T →
    A ⊓ (transfiniteFiltration p δ : AddSubgroup G) ≤ K →
    ∀ (n : ℕ) (a : Fin n → G), (∀ j, a j ∈ A) → ∀ φ : Formula n,
    Complexity .sigma (1 : Ordinal.{v}) φ →
    φ.RealizeIn (transfiniteFiltration p δ : AddSubgroup (G ⧸ T))
      (fun j => (QuotientAddGroup.mk' T) (a j)) →
    φ.RealizeIn (transfiniteFiltration p δ : AddSubgroup G) a

end LogicLineages.ModelsAlgebra.PGroups.Targets
