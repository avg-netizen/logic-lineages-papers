module
public import LogicLineages.PersistentMarking.NumberedWindowInternalRawRepackProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRawRepackCasesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowInternalSparseParsedFoldSyntaxProof (positiveGraph)
open NumberedWindowInternalRawRepackProof (rawMatrix exact_OriginalRawRepack)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Eliminate the actual packed parser preimage for any object goal,
using the same original scratch, no arbitrary original raw selector. -/
theorem exact_OriginalRawRepackCases (scratch : OTerm α) (goal : Formula α)
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (raw : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (positiveGraph raw (scratch.relabel j))) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  obtain ⟨e⟩ := exact_OriginalRawRepack (B := B) (Γ := Γ) scratch
  let j : α → α ⊕ Fin 1 := Sum.inl
  let n : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let Δ := rawMatrix scratch :: Γ.map (fun f => f.relabel j)
  obtain ⟨d⟩ := next (α ⊕ Fin 1) j Δ n
    (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.existentialElimination e d⟩

#print axioms exact_OriginalRawRepackCases
end LogicLineages.PersistentMarking.NumberedWindowInternalRawRepackCasesProof
