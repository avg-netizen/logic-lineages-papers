module
public import LogicLineages.ModelsAlgebra.PGroups.RelativizedDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.QuotientFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary GroupBackAndForth
universe u v

def groupTerminalSigmaTwoTransfer : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (δ : Ordinal.{v}) (K T : AddSubgroup G),
    (transfiniteFiltration p δ : AddSubgroup G) = K ⊔ T → Disjoint K T →
    BackAndForth (2 : Ordinal.{v})
      (Fin.elim0 : Fin 0 → (transfiniteFiltration p δ : AddSubgroup G))
      (Fin.elim0 : Fin 0 → K) → ∀ φ : Formula 0,
    Complexity .sigma (2 : Ordinal.{v}) φ →
    φ.RealizeIn (transfiniteFiltration p δ : AddSubgroup (G ⧸ T)) Fin.elim0 →
    φ.RealizeIn (transfiniteFiltration p δ : AddSubgroup G) Fin.elim0

end LogicLineages.ModelsAlgebra.PGroups.Targets
