module

public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOrderedSelectorsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalFiniteBlocksSubstitutionProof (renameIdentity)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelope (applyUnary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (Reports inputsRename moveReport)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)

abbrev D (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α)) (f : Formula α) :=
  Nonempty (Derivation B Γ f)

/-- The actual ordered selectors can be bound at an arbitrary program
cursor, not just the tail of a tagged node. Each reported position has
the original graph at exactly that cursor. -/
theorem selectorCases (B : Positive (Fin 1)) (arity : Nat) :
    ∀ (α : Type) (Γ : List (Formula α)) (w : OTerm α) (cursor : Program 1) (goal : Formula α),
      (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (values : List (OTerm β)),
        (∀ f ∈ Γ, f.relabel j ∈ Δ) → values.length = arity →
        Reports B Δ (w.relabel j) cursor values → D B Δ (goal.relabel j)) → D B Γ goal := by
  induction arity with
  | zero =>
    intro α Γ w cursor goal next
    have one := next α id Γ [] (fun f h => by simpa only [renameIdentity] using h) rfl trivial
    simpa only [renameIdentity] using one
  | succ arity ih =>
    intro α Γ w cursor goal next
    apply programCases (applyUnary cellHead cursor) ![w] goal
    intro β j Δ field keep first
    rw [inputsRename] at first
    apply ih β Δ (w.relabel j) (applyUnary cellTail cursor) (goal.relabel j)
    intro γ k Ω rest retain size others
    have keeps (f : Formula α) (h : f ∈ Γ) : f.relabel (k ∘ j) ∈ Ω := by
      simpa only [formulaRelabelComposition] using retain _ (keep f h)
    have head := moveReport k Ω retain (applyUnary cellHead cursor) field (w.relabel j) first
    have actual : Reports B Ω (w.relabel (k ∘ j)) cursor (field.relabel k :: rest) :=
      ⟨by simpa only [Term.relabel_relabel] using head,by simpa only [Term.relabel_relabel] using others⟩
    have result := next γ (k ∘ j) Ω (field.relabel k :: rest) keeps (by simp [size]) actual
    simpa only [formulaRelabelComposition] using result

#print axioms selectorCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOrderedSelectorsProof
