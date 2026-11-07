module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSuccessorEliminationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalRecursionGraph
open SourceComputabilityFormulaSupportProof InternalRecursionClosure InternalRecursionClosureSyntaxProof
open InternalGraphCompositionSyntaxProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphSyntaxProof InternalRecursionGraphStepSyntaxProof InternalClosedProgramsBindingProof
open InternalPositiveUnfoldingSupportProof InternalSourceInversionSupportProof
open InternalTagArithmeticSyntaxProof (emb z suc bindEmbedding liftBind varBind)

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem closedApply {p q : Formula α}
    (h : Nonempty (Derivation body [] (p.imp q))) (d : Nonempty (Derivation body Gamma p)) :
    Nonempty (Derivation body Gamma q) := by
  obtain ⟨h⟩ := h
  obtain ⟨d⟩ := d
  exact ⟨Derivation.implicationElimination (weakenClosed h Gamma) d⟩

/-- The ordinary existential rule supplies a predecessor value and its two
literal successor-equation conjuncts. -/
theorem successorCases {n : Nat} (Gamma : List (Formula α))
    (f : OFormula (Fin (n+1))) (g : OFormula (Fin (n+3)))
    (out t : OTerm α) (xs : Fin n → OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (successorStep f g out t xs)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (v : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (recursion f g v (t.relabel j) (fun i => (xs i).relabel j))) →
      Nonempty (Derivation body Delta (graph g (out.relabel j)
        (Fin.cons (t.relabel j) (Fin.cons v (fun i => (xs i).relabel j))))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  let P := recursion f g (.var (.inr (0 : Fin 1))) (t.relabel Sum.inl)
      (fun i => (xs i).relabel Sum.inl) ⊓
    graph g (out.relabel Sum.inl) (Fin.cons (t.relabel Sum.inl)
      (Fin.cons (.var (.inr 0)) (fun i => (xs i).relabel Sum.inl)))
  let Delta := P :: Gamma.map weaken
  obtain ⟨d⟩ := k (α ⊕ Fin 1) Sum.inl Delta (.var (.inr 0))
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.existentialElimination h d⟩

theorem totalCases {n : Nat} (Gamma : List (Formula α))
    (f : OFormula (Fin (n+1))) (g : OFormula (Fin (n+3)))
    (t : OTerm α) (xs : Fin n → OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (totalAt f g t xs)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (v : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (recursion f g v (t.relabel j) (fun i => (xs i).relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  let P := recursion f g (.var (.inr (0 : Fin 1))) (t.relabel Sum.inl)
    (fun i => (xs i).relabel Sum.inl)
  let Delta := P :: Gamma.map weaken
  obtain ⟨d⟩ := k (α ⊕ Fin 1) Sum.inl Delta (.var (.inr 0))
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.existentialElimination h d⟩

theorem totalIntroduction {n : Nat} (f : OFormula (Fin (n+1))) (g : OFormula (Fin (n+3)))
    (out t : OTerm α) (xs : Fin n → OTerm α)
    (h : Nonempty (Derivation body Gamma (recursion f g out t xs))) :
    Nonempty (Derivation body Gamma (totalAt f g t xs)) := by
  obtain ⟨h⟩ := h
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb out)
  rw [instantiate,bindEmbedding,recursionSubst]
  simpa only [varBind,liftBind] using h

theorem graphExistsCases {n : Nat} (Gamma : List (Formula α))
    (f : OFormula (Fin (n+1))) (xs : Fin n → OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (existsOne
      (graph f (.var (.inr (0 : Fin 1))) (fun i => (xs i).relabel Sum.inl)))))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (v : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (graph f v (fun i => (xs i).relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  let P := graph f (.var (.inr (0 : Fin 1))) (fun i => (xs i).relabel Sum.inl)
  let Delta := P :: Gamma.map weaken
  obtain ⟨d⟩ := k (α ⊕ Fin 1) Sum.inl Delta (.var (.inr 0))
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.existentialElimination h d⟩

theorem uniqueApply {n : Nat} (f : OFormula (Fin (n+1))) (g : OFormula (Fin (n+3)))
    (out other t : OTerm α) (xs : Fin n → OTerm α)
    (h : Nonempty (Derivation body Gamma (uniqueAt f g t xs)))
    (d : Nonempty (Derivation body Gamma (recursion f g out t xs)))
    (e : Nonempty (Derivation body Gamma (recursion f g other t xs))) :
    Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (out.equal other))) := by
  have h' := actualFiniteUniversalElimination body α 2 Gamma (uniqueBody f g t xs)
    (fun i => emb (Fin.cases out (fun _ => other) i)) h
  rw [uniqueBodyWitness] at h'
  obtain ⟨h'⟩ := h'
  obtain ⟨d⟩ := d
  obtain ⟨e⟩ := e
  exact ⟨Derivation.implicationElimination h' (Derivation.conjunctionIntroduction d e)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof
