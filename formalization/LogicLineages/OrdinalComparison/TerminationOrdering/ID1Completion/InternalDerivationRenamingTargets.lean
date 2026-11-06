module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingTargets
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticTransforms
open PositiveArithmeticPredicateSubstitution PositiveArithmeticSchemas InternalCalculus

/-- Literal substitution of an arbitrary invariant, including negative P,
commutes with the ORIGINAL free-variable renaming. -/
def ActualPredicateReplacementRenaming : Prop :=
  ∀ (α β : Type) (f : α → β) (p : Positive α) (theta : Formula (α ⊕ Fin 1)),
  (substitutePredicate p theta).relabel f =
    substitutePredicate (PositiveArithmeticTransforms.relabel f p) (theta.relabel (Sum.map f id))

/-- The exact original expanded-language PA induction schema. -/
def ActualInductionSchemaRenaming : Prop :=
  ∀ (α β : Type) (f : α → β) (theta : Formula (α ⊕ Fin 1)),
  (naturalInductionSchema theta).relabel f =
    naturalInductionSchema (theta.relabel (Sum.map f id))

/-- Both schemas refer to the SAME original one-variable positive body.
No fresh inductive definition or strengthened rule is introduced. -/
def ActualFixedPointSchemasRenaming : Prop :=
  ∀ (body : Positive (Fin 1)) (α β : Type) (f : α → β),
  (closureSchema (bodyWithParameters body α)).relabel f =
    closureSchema (bodyWithParameters body β) ∧
  ∀ theta : Formula (α ⊕ Fin 1),
  (leastnessSchema (bodyWithParameters body α) theta).relabel f =
    leastnessSchema (bodyWithParameters body β) (theta.relabel (Sum.map f id))

/-- Admissibility by transforming ORIGINAL finite proof trees, not by adding
a renaming constructor or using a semantic soundness/reflection principle. -/
def ActualDerivationRenaming : Prop :=
  ∀ (body : Positive (Fin 1)) (α β : Type) (f : α → β)
    (Gamma : List (Formula α)) (phi : Formula α),
  Nonempty (Derivation body Gamma phi) →
  Nonempty (Derivation body (Gamma.map (fun p => p.relabel f)) (phi.relabel f))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingTargets
