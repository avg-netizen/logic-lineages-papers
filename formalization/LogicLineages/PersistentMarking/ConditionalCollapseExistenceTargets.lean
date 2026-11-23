module

public import LogicLineages.PersistentMarking.ConditionalCollapseUniquenessTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalCollapseExistence
open ConditionalTowerCofinality

universe u v

/-- Solvability of the defining clause of (P): whatever values `prev` have
been assigned, some critical `θ` satisfies the clause at `ξ`. Here `prev` is
a total function; only its values below `ξ` are used. -/
def Solvable {I : Type u} {O : Type v} [LT I] [LT O]
    (norm : I → O) (critical : O → Prop) : Prop :=
  ∀ (ξ : I) (prev : I → O), ∃ θ, critical θ ∧ ∀ η, η < ξ → norm η < θ → prev η < θ

/-- The same hypothesis with `prev` given only below `ξ` (a dependent
function). -/
def SolvableBelow {I : Type u} {O : Type v} [LT I] [LT O]
    (norm : I → O) (critical : O → Prop) : Prop :=
  ∀ (ξ : I) (prev : (η : I) → η < ξ → O),
    ∃ θ, critical θ ∧ ∀ η (h : η < ξ), norm η < θ → prev η h < θ

/-- Existence for (P): on a well-founded index order with a well-ordered
value order, solvability of the clause gives a collapse satisfying (P). The
fields `one`, `endpoint`, `a` do not occur in (P) and are arbitrary. Together
with `CharacterizationDeterminesCollapse` (#1484) this makes (P) a definition.
Solvability itself is a hypothesis; it is not established here for any
concrete notation system. -/
def CharacterizationExists : Prop :=
  ∀ (I : Type u) (O : Type v) [LinearOrder I] [WellFoundedLT I] [LinearOrder O]
    [WellFoundedLT O] (norm : I → O) (critical : O → Prop) (one : O) (endpoint : I)
    (a : ℕ → I), Solvable norm critical →
    ∃ psi : I → O, CharacterizationP ⟨psi, norm, critical, one, endpoint, a⟩

/-- Existence from the dependent form of the hypothesis. -/
def CharacterizationExistsBelow : Prop :=
  ∀ (I : Type u) (O : Type v) [LinearOrder I] [WellFoundedLT I] [LinearOrder O]
    [WellFoundedLT O] (norm : I → O) (critical : O → Prop) (one : O) (endpoint : I)
    (a : ℕ → I), SolvableBelow norm critical →
    ∃ psi : I → O, CharacterizationP ⟨psi, norm, critical, one, endpoint, a⟩

/-- The two forms of the hypothesis are equivalent: a partial `prev` below
`ξ` extends to a total one (by `norm ξ` elsewhere), so the dependent form is
not actually weaker. -/
def SolvableIffSolvableBelow : Prop :=
  ∀ (I : Type u) (O : Type v) [LinearOrder I] [LinearOrder O]
    (norm : I → O) (critical : O → Prop),
    Solvable norm critical ↔ SolvableBelow norm critical

end LogicLineages.PersistentMarking.ConditionalCollapseExistence
