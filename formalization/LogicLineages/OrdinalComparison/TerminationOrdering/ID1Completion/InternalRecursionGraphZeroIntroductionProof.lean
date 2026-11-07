module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSuccessorEliminationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaPairCodeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaUniquenessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphZeroIntroductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalRecursionGraph
open InternalRecursionGraphSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalRecursionGraphSuccessorEliminationProof InternalGraphCompositionSyntaxProof
open InternalClosedProgramsBindingProof InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalSourceInversionSupportProof InternalOriginalOrderSyntaxProof InternalOriginalOrderProof
open InternalBetaDivisionSyntaxProof InternalPositiveUnfoldingSupportProof

/-- Equality substitution in only the output slot of the unchanged graph. -/
theorem graphOutputTransport {body : Positive (Fin 1)} {n : Nat} {α : Type}
    (Gamma : List (Formula α)) (f : OFormula (Fin (n+1)))
    (u v : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α)
    (he : Nonempty (Derivation body Gamma (eqn u v)))
    (hf : Nonempty (Derivation body Gamma (graph f u xs))) :
    Nonempty (Derivation body Gamma (graph f v xs)) := by
  obtain ⟨he⟩ := he
  obtain ⟨hf⟩ := hf
  let theta := graph f (.var (.inr (0 : Fin 1))) (fun i => (xs i).relabel Sum.inl)
  have ht : Derivation body Gamma (instantiate theta (emb u)) := by
    rw [graphOutputInstantiate]
    exact hf
  have h := Derivation.equalityElimination theta (emb u) (emb v) he ht
  rw [graphOutputInstantiate] at h
  exact ⟨h⟩

theorem initialIntroduction {body : Positive (Fin 1)} {n : Nat} {α : Type}
    (Gamma : List (Formula α)) (f : OFormula (Fin (n+1)))
    (a b out : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α)
    (hf : Nonempty (Derivation body Gamma (graph f out xs)))
    (hb : Nonempty (Derivation body Gamma (beta a b z out))) :
    Nonempty (Derivation body Gamma (initial f a b xs)) := by
  unfold initial OrdinaryArithmetic.initialGraph
  rw [actualOriginalUniversalEmbedding]
  apply actualFiniteUniversalIntroduction body α 1 Gamma
  let A := a.relabel (Sum.inl : α → α ⊕ Fin 1)
  let B := b.relabel (Sum.inl : α → α ⊕ Fin 1)
  let O := out.relabel (Sum.inl : α → α ⊕ Fin 1)
  let v : OrdinaryArithmetic.Term (α ⊕ Fin 1) := .var (.inr 0)
  let P := beta A B z v
  let Delta := P :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 1))
  have hf' := renameInto hf Sum.inl Delta (fun p hp =>
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [graphRename] at hf'
  have hb' := renameInto hb Sum.inl Delta (fun p hp =>
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [betaRename,zRelabel] at hb'
  obtain ⟨hb'⟩ := hb'
  obtain ⟨unique⟩ := InternalBetaUniquenessProof.actualOriginalBetaUniqueness body (α ⊕ Fin 1) A B z O v
  rw [onEquality] at unique
  have he : Nonempty (Derivation body Delta (eqn O v)) :=
    ⟨Derivation.implicationElimination (weakenClosed unique Delta)
      (Derivation.conjunctionIntroduction hb' (Derivation.hypothesis List.mem_cons_self))⟩
  obtain ⟨d⟩ := graphOutputTransport Delta f O v (fun i => (xs i).relabel Sum.inl) he hf'
  exact ⟨Derivation.implicationIntroduction d⟩

theorem stepZero {body : Positive (Fin 1)} {n : Nat} {α : Type}
    (Gamma : List (Formula α)) (g : OFormula (Fin (n+3)))
    (a b : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α) :
    Nonempty (Derivation body Gamma (step g a b z xs)) := by
  rw [stepAsBlock]
  apply actualFiniteUniversalIntroduction body α 3 Gamma
  simp only [stepBody,zRelabel]
  let j : OrdinaryArithmetic.Term (α ⊕ Fin 3) := .var (.inr 0)
  obtain ⟨noLess⟩ := InternalLeastNumberProof.actualNothingBelowZero body (α ⊕ Fin 3) j
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  apply Derivation.explosion
  apply Derivation.implicationElimination (weakenClosed noLess _)
  exact Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self))

theorem actualOriginalRecursionZeroIntroduction :
    InternalRecursionGraphTargets.ActualOriginalRecursionZeroIntroduction := by
  intro body n α f g out xs
  let Gamma := [graph f out xs]
  let a := InternalBetaPairCode.firstCode out z
  let b := InternalBetaPairCode.secondCode out z
  obtain ⟨pair⟩ := InternalBetaPairCodeProof.actualExplicitPairCode body α out z
  have hb : Nonempty (Derivation body Gamma (beta a b z out)) :=
    ⟨Derivation.conjunctionLeft (weakenClosed pair Gamma)⟩
  have hi := initialIntroduction Gamma f a b out xs ⟨Derivation.hypothesis List.mem_cons_self⟩ hb
  obtain ⟨d⟩ := recursionIntroduction Gamma f g a b out z xs hi (stepZero Gamma g a b xs) hb
  exact ⟨Derivation.implicationIntroduction d⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphZeroIntroductionProof
