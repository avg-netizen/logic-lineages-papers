module

public import LogicLineages.ModelsAlgebra.PGroups.BoundedUlmTableDefinitions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u v

/-- The existing literal finite-list fold preserves every positive Pi rank. -/
def groupPositivePiAllComplexity : Prop :=
  ∀ (α : Ordinal.{v}), α ≠ 0 → ∀ (n : ℕ) (fs : List (Formula n)),
    (∀ φ ∈ fs, Complexity .pi α φ) → Complexity .pi α (piTwoAll fs)

def groupUlmRankEntry : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (j n : ℕ) (entry : Option ℕ),
    Complexity .pi (3 : Ordinal.{v}) (ulmRankEntry p j n entry) ∧
      ∀ (G : Type u) [AddCommGroup G] [Countable G] (a : Fin n → G),
        (ulmRankEntry p j n entry).Realize a ↔
          Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) =
            (match entry with | none => Cardinal.aleph0 | some m => (m : Cardinal.{u}))

/-- Exact complete bounded algebraic invariant data only: no isomorphism or
Scott property is assumed or concluded. N=0 is explicitly included. -/
def groupBoundedUlmTable : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N : ℕ) (entries : Fin N → Option ℕ),
    Complexity .pi (3 : Ordinal.{v}) (boundedUlmTable p N entries) ∧
      ∀ (G : Type u) [AddCommGroup G] [Countable G],
        (boundedUlmTable p N entries).Realize (Fin.elim0 : Fin 0 → G) ↔
          finiteFiltration p N = (⊥ : AddSubgroup G) ∧
            ∀ i : Fin N,
              Module.rank (ZMod p) (UlmLayer p (finiteFiltration p i.val : AddSubgroup G)) =
                (match entries i with | none => Cardinal.aleph0 | some m => (m : Cardinal.{u}))

end LogicLineages.ModelsAlgebra.PGroups.Targets
