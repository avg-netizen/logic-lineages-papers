module
public import LogicLineages.ModelsAlgebra.PGroups.TermClosureTargets
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryDefinitions
public import Mathlib.Data.Nat.Prime.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupBackAndForth GroupInfinitary
universe u

def groupFiniteAtomicIsolation : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (n : ℕ) (a : Fin n → G),
    Finite (AddSubgroup.closure (Set.range a)) →
    ∃ q : QF n, q.Realize a ∧
      ∀ (H : Type u) [AddCommGroup H] (b : Fin n → H), q.Realize b ↔ AtomicAgreement a b

def groupPPrimaryAtomicIsolation : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (G : Type u) [AddCommGroup G],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → ∀ (n : ℕ) (a : Fin n → G),
    ∃ q : QF n, q.Realize a ∧
      ∀ (H : Type u) [AddCommGroup H] (b : Fin n → H), q.Realize b ↔ AtomicAgreement a b

end LogicLineages.ModelsAlgebra.PGroups.Targets
