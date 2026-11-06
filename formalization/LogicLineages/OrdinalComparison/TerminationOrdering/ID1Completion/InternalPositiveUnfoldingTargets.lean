module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourcePresentationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingTargets
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticPredicateSubstitution PositiveArithmeticSchemas
open InternalCalculus SourceComputabilityFormulaSupportProof

/-- Actual internal contraction of a positive formula after replacing I by
its defining body. Arithmetic antecedents are unchanged. No semantic premise. -/
def ActualPositiveContraction : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (p : Positive α),
  Nonempty (Derivation body []
    ((substitutePredicate p (bodyWithParameters body α).formula).imp p.formula))

/-- The exact leastness-step proof for the body itself is CONSTRUCTED,
not supplied as an assumption. This is not a computability closure step. -/
def ActualBodyInvariantStep : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type),
  Nonempty (Derivation body
    [replacedBody body (bodyWithParameters body α).formula]
    (bodyWithParameters body α).formula)

/-- The reverse unfolding direction is derived internally by leastness. -/
def ActualInternalReverseUnfolding : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type),
  Nonempty (Derivation body []
    (allOne (predicateAtObject.imp (bodyWithParameters body α).formula)))

/-- Both directions at every literal term, in the unchanged proof calculus. -/
def ActualInternalUnfolding : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (t : Term α),
  Nonempty (Derivation body []
    ((instantiate predicateAtObject t).iff
      (instantiate (bodyWithParameters body α).formula t)))

/-- The actual original joint-Gamma tagged source body is an instance of the
derived theorem, with no alteration of its checker Programs, tags or rules. -/
def ActualOriginalSourceUnfolding : Prop :=
  ∀ (data : SourcePresentation.Data) (context : Nat) (α : Type) (t : Term α),
  Nonempty (Derivation (SourcePresentation.sourceBody data context) []
    ((instantiate predicateAtObject t).iff
      (instantiate (bodyWithParameters (SourcePresentation.sourceBody data context) α).formula t)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingTargets
