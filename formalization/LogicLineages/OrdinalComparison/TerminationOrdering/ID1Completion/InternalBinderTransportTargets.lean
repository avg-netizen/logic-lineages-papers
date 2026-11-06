module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinderTransportTargets
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticPredicateSubstitution
open InternalCalculus SourceComputabilityFormulaSupportProof

/-- Literal syntax transport, not equivalence in a model. -/
def ActualRelabelSubstitution : Prop :=
  ∀ (α β γ : Type) (phi : Formula α) (f : α → β) (ts : β → Term γ),
  (phi.relabel f).subst ts = phi.subst (ts ∘ f)

/-- Move a free-variable renaming through the original singleton binder. -/
def ActualUniversalRenaming : Prop :=
  ∀ (α β : Type) (f : α → β) (phi : Formula (α ⊕ Fin 1)),
  (allOne phi).relabel f = allOne (phi.relabel (Sum.map f id))

/-- Introducing a fresh parameter and immediately instantiating the bound
slot with that same variable returns the EXACT original formula. -/
def ActualFreshInstantiation : Prop :=
  ∀ (α : Type) (phi : Formula (α ⊕ Fin 1)),
  instantiate (liftPredicateFormula phi) (.var (.inr 0)) = phi

/-- Existing positive renaming and ordinary formula renaming are literally
the same syntax, including underneath every original universal binder. -/
def ActualPositiveRenaming : Prop :=
  ∀ (α β : Type) (f : α → β) (p : Positive α),
  (PositiveArithmeticTransforms.relabel f p).formula = p.formula.relabel f

/-- An actual finite proof-tree construction. A supplied CLOSED implication
proof is transported through universal quantification; no semantic truth,
source closure, or extra derivation rule is assumed. -/
def ActualInternalUniversalTransport : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (phi psi : Formula (α ⊕ Fin 1)),
  Nonempty (Derivation body [] (phi.imp psi)) →
  Nonempty (Derivation body [] ((allOne phi).imp (allOne psi)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinderTransportTargets
