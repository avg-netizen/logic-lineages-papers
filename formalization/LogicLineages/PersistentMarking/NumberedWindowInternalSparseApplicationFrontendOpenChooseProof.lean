module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenGateProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenChooseProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases programCompositionCases)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowGuardedGraphTargets (atSlot)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult rawDomain rawCodomain rawLeast)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseApplicationFrontendOpenGateProof (args)

attribute [local irreducible] programGraph

abbrev selectors : Fin 8 → Program 3 :=
  ![atSlot rawContext 0,atSlot rawResult 0,atSlot rawDomain 0,atSlot rawCodomain 0,
    atSlot rawLeast 0,atSlot rawContext 1,atSlot rawResult 1,atSlot rawLeast 1]

abbrev Observed (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (xs : Fin 3 → OTerm α) (ys : Fin 8 → OTerm α) : Prop :=
  ∀ j, Nonempty (Derivation body Γ (programGraph (selectors j) (ys j) xs))

private abbrev projected : Program 8 := .projection 0
private abbrev collector : Program 3 := .composition projected selectors

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem unpackCollector (f u y out : OTerm α) (goal : Formula α)
    (known : Nonempty (Derivation body Γ (programGraph collector out (args f u y))))
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (ys : Fin 8 → OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Observed body Δ (args (f.relabel j) (u.relabel j) (y.relabel j)) ys →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  apply programCompositionCases projected selectors out (args f u y) goal known
  intro β j ys Δ hJ _ observed
  have actual (a : Fin 8) : Nonempty (Derivation body Δ (programGraph (selectors a) (ys a)
      (args (f.relabel j) (u.relabel j) (y.relabel j)))) := by
    have field := observed a
    rw [tripleInputsRename] at field
    exact field
  exact k β j Δ ys hJ actual

/-- Open all the actual original selectors on one and the same tape,
using original totality/composition. The collector's projected result
does not occur in the public continuation. -/
theorem choose (f u y : OTerm α) (goal : Formula α)
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (ys : Fin 8 → OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Observed body Δ (args (f.relabel j) (u.relabel j) (y.relabel j)) ys →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  apply programCases collector (args f u y) goal
  intro β j Δ out hJ read
  rw [tripleInputsRename] at read
  apply unpackCollector (f.relabel j) (u.relabel j) (y.relabel j) out (goal.relabel j) read
  intro γ k' Ξ ys hK seen
  have h (a : Formula α) (ha : a ∈ Γ) : a.relabel (k' ∘ j) ∈ Ξ := by
    rw [← formulaRelabelComposition j k' a]
    exact hK (a.relabel j) (hJ a ha)
  rw [formulaRelabelComposition j k' goal]
  have readAgain : Observed body Ξ
      (args (f.relabel (k' ∘ j)) (u.relabel (k' ∘ j)) (y.relabel (k' ∘ j))) ys := by
    intro a
    have field := seen a
    simp only [Term.relabel_relabel] at field
    exact field
  exact k γ (k' ∘ j) Ξ ys h readAgain

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenChooseProof
