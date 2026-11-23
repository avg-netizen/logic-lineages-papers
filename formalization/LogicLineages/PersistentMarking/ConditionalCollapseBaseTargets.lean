module

public import LogicLineages.PersistentMarking.ConditionalTowerCofinalityTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalCollapseBase
open ConditionalTowerCofinality

universe u v

/-- Under (P), the collapse at an index with nothing below it is the least
critical value: its clause is vacuous. (The abstract form of the first
calibration instance.) -/
def CollapseAtMinimalIndex : Prop :=
  ∀ (I : Type u) (O : Type v) [LinearOrder I] [LinearOrder O] (D : CollapseData I O),
    CharacterizationP D → ∀ ξ : I, (∀ η, ¬ η < ξ) →
      D.critical (D.psi ξ) ∧ ∀ θ, D.critical θ → D.psi ξ ≤ θ

/-- Under (P), every collapse value is at least the collapse at a minimal
index: the least critical value is a lower bound for the whole collapse. -/
def CollapseAboveMinimalValue : Prop :=
  ∀ (I : Type u) (O : Type v) [LinearOrder I] [LinearOrder O] (D : CollapseData I O),
    CharacterizationP D → ∀ ξ₀ : I, (∀ η, ¬ η < ξ₀) → ∀ ξ : I, D.psi ξ₀ ≤ D.psi ξ

/-- Under (P), if `η < ξ` and the norm of `η` is below the least critical
value, then `psi η < psi ξ`: on indices of small norm the collapse is
strictly increasing. -/
def CollapseIncreasingOnSmallNorm : Prop :=
  ∀ (I : Type u) (O : Type v) [LinearOrder I] [LinearOrder O] (D : CollapseData I O),
    CharacterizationP D → ∀ ξ₀ : I, (∀ η, ¬ η < ξ₀) →
      ∀ η ξ : I, η < ξ → D.norm η < D.psi ξ₀ → D.psi η < D.psi ξ

end LogicLineages.PersistentMarking.ConditionalCollapseBase
