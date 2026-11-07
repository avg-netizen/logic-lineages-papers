module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphZeroEliminationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalRecursionGraph
open InternalRecursionGraphSyntaxProof InternalGraphCompositionSyntaxProof InternalClosedProgramsBindingProof
open InternalFiniteBlocksProof InternalTagArithmeticSyntaxProof InternalSourceInversionSupportProof

/-- Eliminate the original finite existential block and expose its three
literal conjuncts. No totality or uniqueness premise is introduced. -/
theorem recursionCases {body : Positive (Fin 1)} {n : Nat} {α : Type}
    (Gamma : List (Formula α)) (f : OFormula (Fin (n+1))) (g : OFormula (Fin (n+3)))
    (out t : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α) (psi : Formula α)
    (d : Nonempty (Derivation body Gamma (recursion f g out t xs)))
    (h : ∀ (β : Type) (j : α → β) (a b : OrdinaryArithmetic.Term β) (Delta : List (Formula β)),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (initial f a b (fun i => (xs i).relabel j))) →
      Nonempty (Derivation body Delta (step g a b (t.relabel j) (fun i => (xs i).relabel j))) →
      Nonempty (Derivation body Delta (beta a b (t.relabel j) (out.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  rw [actualOriginalRecursionInstance] at d
  apply actualFiniteExistentialElimination body α 2 Gamma _ psi d
  let M := arithmeticEmbedding.onFormula (InternalRecursionGraph.matrix f g out t xs)
  let Delta := M :: Gamma.map (fun p => p.relabel Sum.inl)
  apply h (α ⊕ Fin 2) Sum.inl (.var (.inr 0)) (.var (.inr 1)) Delta
  · intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self))⟩
  · exact ⟨Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self))⟩
  · exact ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩

theorem initialElimination {body : Positive (Fin 1)} {n : Nat} {α : Type}
    (Gamma : List (Formula α)) (f : OFormula (Fin (n+1))) (a b out : OrdinaryArithmetic.Term α)
    (xs : Fin n → OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (initial f a b xs)))
    (hb : Nonempty (Derivation body Gamma (beta a b OrdinaryArithmetic.zeroTerm out))) :
    Nonempty (Derivation body Gamma (graph f out xs)) := by
  unfold initial OrdinaryArithmetic.initialGraph at h
  rw [actualOriginalUniversalEmbedding] at h
  have d := actualFiniteUniversalElimination body α 1 Gamma _ (fun _ => emb out) h
  rw [initialWitness] at d
  obtain ⟨d⟩ := d
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.implicationElimination d hb⟩

theorem actualOriginalRecursionZeroElimination :
    InternalRecursionGraphTargets.ActualOriginalRecursionZeroElimination := by
  intro body n α f g out xs
  let Gamma := [recursion f g out OrdinaryArithmetic.zeroTerm xs]
  have h : Nonempty (Derivation body Gamma (graph f out xs)) := by
    apply recursionCases Gamma f g out OrdinaryArithmetic.zeroTerm xs _
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    intro β j a b Delta _ hi _ hb
    rw [graphRename]
    simp only [zRelabel] at hb
    exact initialElimination Delta f a b (out.relabel j) (fun i => (xs i).relabel j) hi hb
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphZeroEliminationProof
