module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedMeasureTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedMeasurePairCasesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition weakenClosed)
open ID1Completion.InternalUnpair (left right)
open ID1Completion.InternalUnpairReverseProof (actualOriginalUnpairReverseInverse)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename moveReport)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem codePairCases (m : OTerm α) (goal : Formula α)
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (d w : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (codePair (m.relabel j) d w)) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  apply programCases left ![m] goal
  intro β j Δ d keep first
  rw [inputsRename] at first
  apply programCases right ![m.relabel j] (goal.relabel j)
  intro γ k Ξ w retain second
  rw [inputsRename] at second
  have both (p : Formula α) (hp : p ∈ Γ) : p.relabel (k ∘ j) ∈ Ξ := by
    rw [← formulaRelabelComposition j k p]
    exact retain (p.relabel j) (keep p hp)
  have moved := moveReport k Ξ retain left d (m.relabel j) first
  simp only [Term.relabel_relabel] at moved second
  obtain ⟨inverse⟩ := actualOriginalUnpairReverseInverse body γ (m.relabel (k ∘ j)) (d.relabel k) w
  obtain ⟨left⟩ := moved
  obtain ⟨right⟩ := second
  have pair := Derivation.implicationElimination (weakenClosed inverse Ξ)
    (Derivation.conjunctionIntroduction left right)
  rw [formulaRelabelComposition j k goal]
  exact next γ (k ∘ j) Ξ (d.relabel k) w both ⟨pair⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedMeasurePairCasesProof
