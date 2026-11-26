module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityScratchBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalitySeedProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem scratchCases (cursor current : OTerm α) (goal : Formula α)
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (seed : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (scratchGraph seed (cursor.relabel j) (current.relabel j))) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  apply programCases consCode (![cursor,current] : Fin 2 → OTerm α) goal
  intro β j Δ seed hJ h
  rw [binaryInputsRename] at h
  exact k β j Δ seed hJ h

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalitySeedProof
