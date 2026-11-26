module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsSelectorsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalFiniteBlocksSubstitutionProof (renameIdentity)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelope (applyUnary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename moveReport Reports)

/-- Select the original head at each actual cursor, in order. The
guarded packing theorem separately excludes malformed/default reads. -/
theorem selectorCases (body : Positive (Fin 1)) (arity : Nat) :
    ∀ (α : Type) (Γ : List (Formula α)) (q : OTerm α) (src : Program 1) (goal : Formula α),
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (fields : List (OTerm β)),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      fields.length = arity →
      Reports body Δ (q.relabel j) src fields →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal) := by
  induction arity with
  | zero =>
    intro α Γ q src goal next
    have keep (p : Formula α) (hp : p ∈ Γ) : p.relabel id ∈ Γ := by
      simpa only [renameIdentity] using hp
    have done := next α id Γ [] keep rfl True.intro
    simpa only [renameIdentity] using done
  | succ count ih =>
    intro α Γ q src goal next
    let select := applyUnary cellHead src
    apply programCases select ![q] goal
    intro β j Δ head keep row
    rw [inputsRename] at row
    apply ih β Δ (q.relabel j) (applyUnary cellTail src) (goal.relabel j)
    intro γ k Ξ tail retain len rest
    have both (p : Formula α) (hp : p ∈ Γ) : p.relabel (k ∘ j) ∈ Ξ := by
      rw [← formulaRelabelComposition j k p]
      exact retain (p.relabel j) (keep p hp)
    have first := moveReport k Ξ retain select head (q.relabel j) row
    simp only [Term.relabel_relabel] at first rest
    rw [formulaRelabelComposition j k goal]
    exact next γ (k ∘ j) Ξ (head.relabel k :: tail) both
      (by simpa only [List.length_cons,len]) ⟨first,rest⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsSelectorsProof
