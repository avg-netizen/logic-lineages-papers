module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusTargets
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticSchemas
open SourceComputabilityFormulaSupportProof ID1Completion.InternalCalculus

def ActualInternalCalculusSoundness : Prop :=
  ∀ (body : Positive (Fin 1)) (P : Nat → Prop), InductiveModel body P →
  ∀ (α : Type) (Gamma : List (Formula α)) (phi : Formula α),
  Nonempty (Derivation body Gamma phi) →
  ∀ v : α → Nat, (∀ p, p ∈ Gamma → realize P p v) → realize P phi v

def ActualStandardLeastModel : Prop :=
  ∀ body : Positive (Fin 1), InductiveModel body (standardLeastPredicate body)

/-- The invariant may contain the inductive predicate negatively and may
retain any finite collection of typed-computability/constructor parameters. -/
def ActualInternalInvariantInduction : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α))
    (theta : Formula (α ⊕ Fin 1)),
  Nonempty (Derivation body (replacedBody body theta :: Gamma.map weaken) theta) →
  Nonempty (Derivation body Gamma (allOne ((predicateAtObject (α := α)).imp theta)))

def ActualInternalNaturalInduction : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α))
    (theta : Formula (α ⊕ Fin 1)),
  Nonempty (Derivation body Gamma (instantiate theta (arithmeticEmbedding.onTerm OrdinaryArithmetic.zeroTerm))) →
  Nonempty (Derivation body (theta :: Gamma.map weaken) (successorInstance theta)) →
  Nonempty (Derivation body Gamma (allOne theta))

/-- An exact first-order invariant, with the induction conclusion available
at every literal term. This is syntactic instantiation, not N-realization. -/
def ActualInternalInvariantInstance : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α))
    (theta : Formula (α ⊕ Fin 1)) (t : Term α),
  Nonempty (Derivation body (replacedBody body theta :: Gamma.map weaken) theta) →
  Nonempty (Derivation body Gamma (instantiate ((predicateAtObject (α := α)).imp theta) t))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusTargets
