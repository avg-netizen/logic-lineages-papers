module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTwoHopTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityFormulaProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFinitePathEliminationProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialElimination)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePositiveTransitivityFormulaProof (suppliedRename)
open NumberedWindowInternalCoverCombinedRestrictedTwoHopTargets
attribute [local irreducible] programGraph

variable {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5)

theorem pathDataRename {β : Type} (ctx cod src dst left right : OTerm α) (j : α → β) :
    (pathData C X W s raw ctx cod src dst left right).relabel j = pathData C X W s raw
      (ctx.relabel j) (cod.relabel j) (src.relabel j) (dst.relabel j) (left.relabel j) (right.relabel j) := by
  simp only [pathData,conjunctionRename,leastRename,suppliedRename]

theorem suppliedPathCases {body : Positive (Fin 1)} {Γ : List (Formula α)}
    (ctx cod src dst : OTerm α) (goal : Formula α)
    (known : Nonempty (Derivation body Γ (suppliedPath C X W s raw ctx cod src dst)))
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (left right : OTerm β),
      (∀ a ∈ Γ, a.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (pathData C X W s raw (ctx.relabel j) (cod.relabel j)
        (src.relabel j) (dst.relabel j) left right)) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  let j : α → α ⊕ Fin 2 := Sum.inl
  let row := pathRow C X W s raw ctx cod src dst
  let Δ := row :: Γ.map (fun p => p.relabel j)
  apply actualFiniteExistentialElimination body α 2 Γ row goal known
  have keep (p : Formula α) (hp : p ∈ Γ) : p.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have here : Nonempty (Derivation body Δ row) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact k (α ⊕ Fin 2) j Δ (.var (.inr 0)) (.var (.inr 1)) keep here

#print axioms pathDataRename
#print axioms suppliedPathCases
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFinitePathEliminationProof
