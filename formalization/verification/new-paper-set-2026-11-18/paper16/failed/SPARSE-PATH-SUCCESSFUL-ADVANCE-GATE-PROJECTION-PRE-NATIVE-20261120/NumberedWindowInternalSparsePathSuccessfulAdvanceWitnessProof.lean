module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceWitnessProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialIntroduction actualFiniteExistentialElimination)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets
open NumberedWindowInternalSparsePathSuccessfulAdvanceSyntaxProof (reports rowWitness)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem supply {raw : Program 5} {least : Program 3}
    (ctx ty current hop target q w r : OTerm α)
    (known : Nonempty (Derivation body Γ (hopCalls raw least ctx ty current hop target q w r))) :
    Nonempty (Derivation body Γ (someHopCalls raw least ctx ty current hop target)) := by
  apply actualFiniteExistentialIntroduction body α 3 Γ (hopCallRow raw least ctx ty current hop target)
    (fun i => emb (reports q w r i))
  rw [rowWitness]
  exact known

theorem reportCases (raw : Program 5) (least : Program 3)
    (ctx ty current hop target : OTerm α) (goal : Formula α)
    (known : Nonempty (Derivation body Γ (someHopCalls raw least ctx ty current hop target)))
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (q w r : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (hopCalls raw least (ctx.relabel j) (ty.relabel j)
        (current.relabel j) (hop.relabel j) (target.relabel j) q w r)) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  let j : α → α ⊕ Fin 3 := Sum.inl
  let row := hopCallRow raw least ctx ty current hop target
  let Δ := row :: Γ.map (fun p => p.relabel j)
  apply actualFiniteExistentialElimination body α 3 Γ row goal known
  have hJ (p : Formula α) (hp : p ∈ Γ) : p.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have h : Nonempty (Derivation body Δ row) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact k (α ⊕ Fin 3) j Δ (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) hJ h

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceWitnessProof
