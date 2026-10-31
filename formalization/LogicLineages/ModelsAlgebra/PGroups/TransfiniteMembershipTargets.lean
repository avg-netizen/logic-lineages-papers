module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteMembershipDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupBackAndForth GroupInfinitary
universe u

def piAndQFExact : Prop :=
  ∀ (α : Ordinal.{0}) (n : ℕ) (φ : Formula n) (q : QF n),
    Complexity .pi α φ → Complexity .pi α (piAndQF φ q) ∧
    ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
      (piAndQF φ q).Realize a ↔ φ.Realize a ∧ q.Realize a

/-- Actual ordinary countable syntax in the original language, uniformly valid
in all abelian groups. No semantic predicate is inserted as a formula leaf. -/
def omegaBlockMembershipDefinable : Prop :=
  ∀ (p : ℕ) (γ : Ordinal.{0}) [Countable γ.ToType] (n : ℕ) (t : GroupTerm n),
    ∃ φ : Formula n, Complexity .pi (2*γ) φ ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
        φ.Realize a ↔ t.eval a ∈ (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G)

def finiteOffsetMembershipDefinable : Prop :=
  ∀ (p : ℕ) (γ : Ordinal.{0}) [Countable γ.ToType] (r n : ℕ) (t : GroupTerm n),
    ∃ φ : Formula n, Complexity .sigma (2*γ+1) φ ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
        φ.Realize a ↔ t.eval a ∈ (transfiniteFiltration p (Ordinal.omega0*γ+r) : AddSubgroup G)
end LogicLineages.ModelsAlgebra.PGroups.Targets
