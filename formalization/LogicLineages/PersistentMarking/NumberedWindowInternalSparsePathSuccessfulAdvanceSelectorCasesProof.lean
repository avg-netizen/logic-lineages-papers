module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceSelectorCasesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases programCompositionCases)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelope (hopSource hopWitness hopRawTarget)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (oneRename)

private abbrev selectors : Fin 3 → Program 1 := ![hopSource,hopWitness,hopRawTarget]
private abbrev projected : Program 3 := .projection (0 : Fin 3)
private abbrev collector : Program 1 := .composition projected selectors

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The existing graph-composition eliminator opens all three actual
selector calls. Its projected result is discarded, not a witness oracle. -/
private theorem opening (hop value : OTerm α) (goal : Formula α)
    (known : Nonempty (Derivation body Γ (unary collector value hop)))
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (q w r : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (unary hopSource q (hop.relabel j))) →
      Nonempty (Derivation body Δ (unary hopWitness w (hop.relabel j))) →
      Nonempty (Derivation body Δ (unary hopRawTarget r (hop.relabel j))) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  apply programCompositionCases projected selectors value (![hop] : Fin 1 → OTerm α) goal known
  intro β j ys Δ hJ _ read
  have fields (i : Fin 3) : Nonempty (Derivation body Δ (unary (selectors i) (ys i) (hop.relabel j))) := by
    have d := read i
    rw [oneRename] at d
    exact d
  exact k β j Δ (ys 0) (ys 1) (ys 2) hJ (fields 0) (fields 1) (fields 2)

theorem chooseSelectors (hop : OTerm α) (goal : Formula α)
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (q w r : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (unary hopSource q (hop.relabel j))) →
      Nonempty (Derivation body Δ (unary hopWitness w (hop.relabel j))) →
      Nonempty (Derivation body Δ (unary hopRawTarget r (hop.relabel j))) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  apply programCases collector (![hop] : Fin 1 → OTerm α) goal
  intro β j Δ value hJ known
  rw [oneRename] at known
  apply opening (hop.relabel j) value (goal.relabel j) known
  intro γ f Ξ q w r hF a b c
  have seek (p : Formula α) (hp : p ∈ Γ) : p.relabel (f ∘ j) ∈ Ξ := by
    rw [← formulaRelabelComposition j f p]
    exact hF (p.relabel j) (hJ p hp)
  rw [formulaRelabelComposition j f goal]
  simp only [Term.relabel_relabel] at a b c
  exact k γ (f ∘ j) Ξ q w r seek a b c

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceSelectorCasesProof
