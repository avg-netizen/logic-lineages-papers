module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalCanonicalResultFoldOpening
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Full specialized opening acceptance iff an internally quantified original
application opening. There are NO pre-supplied constructor, tag, child, bound,
calibration, semantic decode or successful-run premises in either direction.
All leaves, positive bodies, variable types, contexts and parent terms vary. -/
def ActualOriginalCanonicalFoldOpeningFactorization : Prop :=
  ∀ (body : Positive (Fin 1)) (valid member : Program 1) (α : Type)
    (Gamma : List (Formula α)) (parent : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((openingAccepted valid member parent).iff (opened valid member parent)))

/-- A relabel-safe elimination interface for later strong-payload induction.
Acceptance is the only graph premise. The continuation receives the original
constructors, root/child validity, codomain membership, parent/child selector
graphs and both strict payload bounds in one shared witness formula. Nothing
is required about a normalized output or its code/payload size. -/
def ActualOriginalCanonicalFoldOpeningContinuation : Prop :=
  ∀ (body : Positive (Fin 1)) (valid member : Program 1) (α : Type)
    (Gamma : List (Formula α)) (parent : OrdinaryArithmetic.Term α) (psi : Formula α),
  Nonempty (Derivation body Gamma (openingAccepted valid member parent)) →
  (∀ (β : Type) (j : α → β) (Delta : List (Formula β))
      (payload middle children arrow d e fp ap fn arg : OrdinaryArithmetic.Term β),
    (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
    Nonempty (Derivation body Delta
      (openingWitnesses valid member (parent.relabel j)
        payload middle children arrow d e fp ap fn arg)) →
    Nonempty (Derivation body Delta (psi.relabel j))) →
  Nonempty (Derivation body Gamma psi)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningTargets
