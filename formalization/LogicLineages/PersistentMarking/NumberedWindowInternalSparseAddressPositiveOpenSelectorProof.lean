module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTapeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenSelectorProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases programCompositionCases)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult rawLeast)
open NumberedWindowInternalSparseAddressPositive (atAddress)
open NumberedWindowInternalSparseAddressPositiveOpenTapeProof (args)

abbrev selectors : Fin 6 → Program 3 := ![atAddress rawContext 0, atAddress rawResult 0, atAddress rawLeast 0,
  atAddress rawContext 2, atAddress rawResult 2, atAddress rawLeast 2]

private abbrev projected : Program 6 := .projection (0 : Fin 6)
private abbrev collector : Program 3 := .composition projected selectors

abbrev Observations (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (xs : Fin 3 → OTerm α) (values : Fin 6 → OTerm α) : Prop :=
  ∀ i, Nonempty (Derivation body Γ (programGraph (selectors i) (values i) xs))

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem unfoldReports (left cert right out : OTerm α) (goal : Formula α)
    (known : Nonempty (Derivation body Γ (programGraph collector out (args left cert right))))
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (values : Fin 6 → OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Observations body Δ (args (left.relabel j) (cert.relabel j) (right.relabel j)) values →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  apply programCompositionCases projected selectors out (args left cert right) goal known
  intro β j values Δ hJ _ observed
  have actual (i : Fin 6) : Nonempty (Derivation body Δ (programGraph (selectors i) (values i)
      (args (left.relabel j) (cert.relabel j) (right.relabel j)))) := by
    have field := observed i
    rw [tripleInputsRename] at field
    exact field
  exact k β j Δ values hJ actual

/-- Choose the six genuine selector outputs at the original two physical
endpoints. The extra projected output is not used as a premise. -/
theorem choose (left cert right : OTerm α) (goal : Formula α)
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (values : Fin 6 → OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Observations body Δ (args (left.relabel j) (cert.relabel j) (right.relabel j)) values →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  apply programCases collector (args left cert right) goal
  intro β j Δ out hJ read
  rw [tripleInputsRename] at read
  apply unfoldReports (left.relabel j) (cert.relabel j) (right.relabel j) out (goal.relabel j) read
  intro γ f Ξ values hF observations
  have h (p : Formula α) (hp : p ∈ Γ) : p.relabel (f ∘ j) ∈ Ξ := by
    rw [← formulaRelabelComposition j f p]
    exact hF (p.relabel j) (hJ p hp)
  rw [formulaRelabelComposition j f goal]
  have seen : Observations body Ξ
      (args (left.relabel (f ∘ j)) (cert.relabel (f ∘ j)) (right.relabel (f ∘ j))) values := by
    intro i
    have field := observations i
    simp only [Term.relabel_relabel] at field
    exact field
  exact k γ (f ∘ j) Ξ values h seen

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenSelectorProof
