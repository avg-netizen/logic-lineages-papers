module
public import LogicLineages.ModelsAlgebra.PGroups.PrimaryZeroSyntaxDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u

def primarySentenceExact : Prop :=
  ∀ p : ℕ, Complexity .pi (2:Ordinal.{0}) (primarySentence p) ∧
    ∀ (G : Type u) [AddCommGroup G],
      (primarySentence p).Realize (Fin.elim0 : Fin 0 → G) ↔ ∀ x : G, ∃ k : ℕ, p^k • x=0

def zeroStageDescriptor : Prop :=
  ∀ (p : ℕ) (γ : Ordinal.{0}) [Countable γ.ToType] (N : ℕ),
    ∃ φ : Formula 0, Complexity .pi (2*γ+1) φ ∧
      ∀ (G : Type u) [AddCommGroup G],
        φ.Realize (Fin.elim0 : Fin 0 → G) ↔
          (transfiniteFiltration p (Ordinal.omega0*γ+N) : AddSubgroup G) = ⊥
end LogicLineages.ModelsAlgebra.PGroups.Targets
