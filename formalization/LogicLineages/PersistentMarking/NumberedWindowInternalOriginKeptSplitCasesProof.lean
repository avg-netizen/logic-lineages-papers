module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptSplitTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptSplitCasesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialElimination)
open NumberedWindowInternalOriginKeptSplitTargets

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Open all eight witness slots from the single actual finite object
existential, preserving the real four occurrence comparator reports. -/
theorem exact_OriginalKeptSplitCases (l r k d : OTerm α) (goal : Formula α)
    (held : Nonempty (Derivation B Γ (splitExists l r k d)))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (w : Fin 8 → OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (evidence (l.relabel j) (r.relabel j) (k.relabel j) (d.relabel j) w)) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  apply actualFiniteExistentialElimination B α 8 Γ (matrix l r k d) goal held
  let j : α → α ⊕ Fin 8 := Sum.inl
  let Δ := matrix l r k d :: Γ.map (fun f => f.relabel j)
  exact next (α ⊕ Fin 8) j Δ (fun i => .var (.inr i))
    (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩

#print axioms exact_OriginalKeptSplitCases
end LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptSplitCasesProof
