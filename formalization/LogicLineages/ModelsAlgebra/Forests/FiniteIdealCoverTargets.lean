module
public import LogicLineages.ModelsAlgebra.Forests.FiniteIdealCoverDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.FiniteIdealCover.Targets

/-- The finite graph-class cover argument of `lem:image-cover`, abstracted
only over its genuine reflexive/transitive embedding relation and actual
hereditary directed cover. This does not assert such a cover can be computed. -/
def FiniteCoverCriterion : Prop :=
  ∀ (α ι : Type) [Fintype ι] [Nonempty ι]
    (R : α → α → Prop) (K : α → Prop) (D : ι → α → Prop),
    (∀ a, R a a) →
    (∀ a b c, R a b → R b c → R a c) →
    (∀ x, K x ↔ ∃ i, D i x) →
    (∀ i, Hereditary R (D i)) →
    (∀ i, JEP R (D i)) →
    (JEP R K ↔ ∃ i, ∀ x, K x → D i x)

end LogicLineages.ModelsAlgebra.Forests.FiniteIdealCover.Targets
