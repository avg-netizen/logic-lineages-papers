module

public import LogicLineages.NativeModule.PersistentMarking.ActualCollapseDefinitions

@[expose] public section

/-! # The diagonal step of the calibration, over abstract data

Frozen before proof (local Fable-trio round, 27 November 2026, root lane).

Paper 16's calibration `Δ_n' = ψ_B(a_n)` passes from one tower level to the next by the same
argument each time: once the collapse is known along a family of indices `p e` below the next tower
argument (`ψ(p e) = L e` as long as `L` has no fixed point up to `e`), the collapse at that
argument is the least fixed point of `L` above the base value. For `n = 3` the family is
`p e = Ω^e`, the argument is `Ω^Ω`, and `L e = B_0^e(N_B)(0)`.

Nothing here mentions orbits, Cantor normal forms or a particular collapse: the statement is for
any `CollapseData` satisfying (P). -/

namespace LogicLineages.PersistentMarking.CollapseDiagonal
open Ordinal ConditionalTowerCofinality OrdinalRealizationTargets
open scoped Ordinal

universe u

/-- What the diagonal step uses. `top` is the next tower argument, `p` the family of indices
below it, `L` the level diagonal, `Γ` the base value (the least critical value). -/
structure DiagonalHypotheses {I : Type u} [LinearOrder I] (D : CollapseData I Ordinal.{0})
    (top : I) (p : CountableOrdinal → I) (L : CountableOrdinal → CountableOrdinal)
    (Γ : CountableOrdinal) : Prop where
  /-- (P). -/
  characterization : CharacterizationP D
  criticalCountable : ∀ θ, D.critical θ → θ < ω₁
  criticalAboveBase : ∀ θ, D.critical θ → Γ.val ≤ θ
  criticalSup : ∀ f : ℕ → Ordinal.{0}, StrictMono f → (∀ n, D.critical (f n)) →
    ∀ θ, IsLUB (Set.range f) θ → D.critical θ
  baseAboveOne : 1 < Γ.val
  /-- `L` is strictly increasing, weakly inflationary, and bounded at limits by its earlier values. -/
  strict : ∀ x y : CountableOrdinal, x.val < y.val → (L x).val < (L y).val
  inflationary : ∀ x : CountableOrdinal, x.val ≤ (L x).val
  limit : ∀ l : CountableOrdinal, Order.IsSuccLimit l.val → ∀ b : Ordinal.{0},
    (∀ e : CountableOrdinal, e.val < l.val → (L e).val ≤ b) → (L l).val ≤ b
  /-- No fixed point of `L` in `[1, Γ]`. -/
  noEarlyFixed : ∀ θ : CountableOrdinal, 1 ≤ θ.val → θ.val ≤ Γ.val → L θ ≠ θ
  /-- The family lies below `top`, has norm at most its parameter, and covers every index below
  `top` whose norm is below the parameter. -/
  below : ∀ e : CountableOrdinal, 1 ≤ e.val → p e < top
  norm : ∀ e : CountableOrdinal, 1 ≤ e.val → D.norm (p e) ≤ e.val
  cover : ∀ η : I, η < top → ∀ e : CountableOrdinal, 1 ≤ e.val → D.norm η < e.val → η < p e
  /-- The collapse along the family, below the first fixed point of `L`. -/
  level : ∀ e : CountableOrdinal, 1 ≤ e.val →
    (∀ θ : CountableOrdinal, 1 ≤ θ.val → θ.val ≤ e.val → L θ ≠ θ) → D.psi (p e) = (L e).val

/-- The diagonal step: the collapse at `top` is the least fixed point of `L` above `Γ`. -/
def DiagonalCollapse : Prop :=
  ∀ (I : Type u) [LinearOrder I] (D : CollapseData I Ordinal.{0}) (top : I)
    (p : CountableOrdinal → I) (L : CountableOrdinal → CountableOrdinal) (Γ : CountableOrdinal),
    DiagonalHypotheses D top p L Γ →
    ∀ fp : CountableOrdinal, L fp = fp → Γ.val < fp.val →
      (∀ θ : CountableOrdinal, Γ.val < θ.val → L θ = θ → fp.val ≤ θ.val) →
      D.psi top = fp.val

end LogicLineages.PersistentMarking.CollapseDiagonal
