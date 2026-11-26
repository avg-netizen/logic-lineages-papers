module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentGuardTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z eqn)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntax)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (Reports)

/-- Reject literal λ at a terminal. The fixed table handles the original
strict auxiliary edges; its type-bit parameters deliberately impose no
typing obligation. This guard is neither intrinsic W nor selected V. -/
def fragmentLeaf : Program 1 := branch (header 2 2) (constantOne 1) (constantZero 1)
abbrev fragmentGuard : Program 1 := auxSyntax fragmentLeaf (constantOne 1)

def ExactOpenCoverAuxFragmentLeaf : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (prior : OTerm α),
    Nonempty (Derivation body Γ (unary fragmentGuard (suc z) (suc prior))) →
    Nonempty (Derivation body Γ (unary termShape z (suc prior))) →
    Nonempty (Derivation body Γ (unary (header 2 2) z (suc prior)))

/-- Genuine held guard report at this arbitrary raw key. The leaf exposes a
real predecessor and both rejection bits; the original tag-six alternative
exposes each physical field, actual strict raw edge, and both same-guard
recursive reports, all in their actual object scope. -/
def ExactOpenCoverAuxFragmentCases : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (raw : OTerm α) (goal : Formula α),
    Nonempty (Derivation body Γ (unary fragmentGuard (suc z) raw)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (prior : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (eqn (raw.relabel j) (suc prior))) →
      Nonempty (Derivation body Δ (unary (header 2 2) z (suc prior))) →
      Nonempty (Derivation body Δ (unary termShape z (suc prior))) →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (dom cod fn arg : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Reports body Δ (raw.relabel j) cellTail [dom,cod,fn,arg] →
      Nonempty (Derivation body Δ (eqn (raw.relabel j) (auxiliaryTerm dom cod fn arg))) →
      Nonempty (Derivation body Δ (ltF fn (raw.relabel j))) →
      Nonempty (Derivation body Δ (ltF arg (raw.relabel j))) →
      Nonempty (Derivation body Δ (unary fragmentGuard (suc z) fn)) →
      Nonempty (Derivation body Δ (unary fragmentGuard (suc z) arg)) →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentGuardTargets
