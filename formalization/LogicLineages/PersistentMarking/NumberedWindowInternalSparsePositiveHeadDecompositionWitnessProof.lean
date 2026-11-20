module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionHeadSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionWitnessProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialIntroduction actualFiniteExistentialElimination)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets
open NumberedWindowInternalSparsePositiveHeadDecompositionHeadSyntaxProof (headValues rowWitness)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem provideHead (raw : Program 5) (least : Program 3)
    (ctx ty source cert target head tail next : OTerm α)
    (known : Nonempty (Derivation body Γ (headData raw least ctx ty source cert target head tail next))) :
    Nonempty (Derivation body Γ (hasAcceptedHead raw least ctx ty source cert target)) := by
  apply actualFiniteExistentialIntroduction body α 3 Γ (headRow raw least ctx ty source cert target)
    (fun i => emb (headValues head tail next i))
  rw [rowWitness]
  exact known

theorem headCases (raw : Program 5) (least : Program 3) (ctx ty source cert target : OTerm α)
    (goal : Formula α)
    (known : Nonempty (Derivation body Γ (hasAcceptedHead raw least ctx ty source cert target)))
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (head tail next : OTerm β),
      (∀ q ∈ Γ, q.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (headData raw least (ctx.relabel j) (ty.relabel j) (source.relabel j)
        (cert.relabel j) (target.relabel j) head tail next)) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  let j : α → α ⊕ Fin 3 := Sum.inl
  let row := headRow raw least ctx ty source cert target
  let Δ := row :: Γ.map (fun p => p.relabel j)
  apply actualFiniteExistentialElimination body α 3 Γ row goal known
  have hJ (q : Formula α) (hq : q ∈ Γ) : q.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have data : Nonempty (Derivation body Δ row) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact k (α ⊕ Fin 3) j Δ (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) hJ data

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionWitnessProof
