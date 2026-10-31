module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteUlmSyntaxDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def transfiniteUlmBoundsDefinable : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (γ : Ordinal.{0}) [Countable γ.ToType] (j m : ℕ),
    ∃ lo hi : Formula 0, Complexity .sigma (2*γ+2) lo ∧ Complexity .pi (2*γ+2) hi ∧
      ∀ (G : Type) [AddCommGroup G],
        (lo.Realize (Fin.elim0 : Fin 0 → G) ↔
          (m:Cardinal) ≤ Module.rank (ZMod p) (UlmLayer p
            (transfiniteFiltration p (Ordinal.omega0*γ+j) : AddSubgroup G))) ∧
        (hi.Realize (Fin.elim0 : Fin 0 → G) ↔
          Module.rank (ZMod p) (UlmLayer p
            (transfiniteFiltration p (Ordinal.omega0*γ+j) : AddSubgroup G)) ≤ (m:Cardinal))

def transfiniteUlmExactDefinable : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (γ : Ordinal.{0}) [Countable γ.ToType] (j m : ℕ),
    ∃ d : DifferenceFormula 0, d.AtLevel (2*γ+2) ∧
      ∀ (G : Type) [AddCommGroup G],
        d.Realize (Fin.elim0 : Fin 0 → G) ↔ Module.rank (ZMod p) (UlmLayer p
          (transfiniteFiltration p (Ordinal.omega0*γ+j) : AddSubgroup G)) = (m:Cardinal)

def transfiniteUlmInfiniteDefinable : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (γ : Ordinal.{0}) [Countable γ.ToType] (j : ℕ),
    ∃ φ : Formula 0, Complexity .pi (2*γ+3) φ ∧
      ∀ (G : Type) [AddCommGroup G],
        φ.Realize (Fin.elim0 : Fin 0 → G) ↔ Cardinal.aleph0 ≤ Module.rank (ZMod p)
          (UlmLayer p (transfiniteFiltration p (Ordinal.omega0*γ+j) : AddSubgroup G))

def countableTransfiniteUlmBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G] (α : Ordinal.{0}),
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) ≤ Cardinal.aleph0
end LogicLineages.ModelsAlgebra.PGroups.Targets
