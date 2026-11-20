module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityScratchBindingProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalScratchCasesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph)
open NumberedWindowInternalSparsePositiveTerminalityTargets (terminalScratch)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Eliminate the actually returned terminal encoded current with the
existing object existential rule. The scratch state itself is unchanged. -/
theorem terminalCases (out : OTerm α) (goal : Formula α)
    (done : Nonempty (Derivation body Γ (terminalScratch out)))
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (current : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (scratchGraph (out.relabel j) z current)) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  obtain ⟨done⟩ := done
  let j : α → α ⊕ Fin 1 := Sum.inl
  let current : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let row := scratchGraph (out.relabel j) z current
  let Δ := row :: Γ.map weaken
  have hJ (p : Formula α) (h : p ∈ Γ) : p.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,h,rfl⟩)
  have given : Nonempty (Derivation body Δ row) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨use⟩ := k (α ⊕ Fin 1) j Δ current hJ given
  exact ⟨Derivation.existentialElimination done use⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalScratchCasesProof
