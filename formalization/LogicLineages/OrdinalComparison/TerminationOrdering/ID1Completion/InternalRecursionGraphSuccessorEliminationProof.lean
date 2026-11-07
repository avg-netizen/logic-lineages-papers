module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphZeroEliminationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSuccessorEliminationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalRecursionGraph
open InternalRecursionGraphSyntaxProof InternalRecursionGraphStepSyntaxProof InternalRecursionGraphZeroEliminationProof
open InternalGraphCompositionSyntaxProof InternalClosedProgramsBindingProof InternalFiniteBlocksProof
open InternalTagArithmeticSyntaxProof InternalSourceInversionSupportProof InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalBetaTotalityProof
open InternalBetaDivisionSyntaxProof InternalQuotientComparisonProof InternalPositiveUnfoldingSupportProof

/-- Instantiate the literal three-variable step guard in evaluator order. -/
theorem stepElimination {body : Positive (Fin 1)} {n : Nat} {α : Type}
    (Gamma : List (Formula α)) (g : OFormula (Fin (n+3)))
    (a b t j v w : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (step g a b t xs)))
    (hj : Nonempty (Derivation body Gamma (ltF j t)))
    (hv : Nonempty (Derivation body Gamma (beta a b j v)))
    (hw : Nonempty (Derivation body Gamma (beta a b (suc j) w))) :
    Nonempty (Derivation body Gamma (graph g w (Fin.cons j (Fin.cons v xs)))) := by
  rw [stepAsBlock] at h
  have d := actualFiniteUniversalElimination body α 3 Gamma _ (fun i => emb (stepValues j v w i)) h
  rw [stepWitness] at d
  obtain ⟨d⟩ := d
  obtain ⟨hj⟩ := hj
  obtain ⟨hv⟩ := hv
  obtain ⟨hw⟩ := hw
  exact ⟨Derivation.implicationElimination d
    (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction hj hv) hw)⟩

/-- Restrict only the existing step guard from succ(t) to t. -/
theorem stepRestriction {body : Positive (Fin 1)} {n : Nat} {α : Type}
    (Gamma : List (Formula α)) (g : OFormula (Fin (n+3)))
    (a b t : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (step g a b (suc t) xs))) :
    Nonempty (Derivation body Gamma (step g a b t xs)) := by
  rw [stepAsBlock]
  apply actualFiniteUniversalIntroduction body α 3 Gamma
  let j : OrdinaryArithmetic.Term (α ⊕ Fin 3) := .var (.inr 0)
  let v : OrdinaryArithmetic.Term (α ⊕ Fin 3) := .var (.inr 1)
  let w : OrdinaryArithmetic.Term (α ⊕ Fin 3) := .var (.inr 2)
  let A := a.relabel (Sum.inl : α → α ⊕ Fin 3)
  let B := b.relabel (Sum.inl : α → α ⊕ Fin 3)
  let T := t.relabel (Sum.inl : α → α ⊕ Fin 3)
  let P := (ltF j T ⊓ beta A B j v) ⊓ beta A B (suc j) w
  let Delta := P :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 3))
  have ds := renameInto h Sum.inl Delta (fun p hp =>
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [stepRename,sucRelabel] at ds
  obtain ⟨ord⟩ := actualRightSuccessorOrder body (α ⊕ Fin 3) j T
  have hj : Nonempty (Derivation body Delta (ltF j (suc T))) :=
    ⟨Derivation.implicationElimination (weakenClosed ord Delta)
      (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)))⟩
  obtain ⟨d⟩ := stepElimination Delta g A B (suc T) j v w
    (fun i => (xs i).relabel Sum.inl) ds hj
    ⟨Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self))⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.implicationIntroduction d⟩

theorem recursionIntroduction {body : Positive (Fin 1)} {n : Nat} {α : Type}
    (Gamma : List (Formula α)) (f : OFormula (Fin (n+1))) (g : OFormula (Fin (n+3)))
    (a b out t : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α)
    (hi : Nonempty (Derivation body Gamma (initial f a b xs)))
    (hs : Nonempty (Derivation body Gamma (step g a b t xs)))
    (hb : Nonempty (Derivation body Gamma (beta a b t out))) :
    Nonempty (Derivation body Gamma (recursion f g out t xs)) := by
  rw [actualOriginalRecursionInstance]
  apply actualFiniteExistentialIntroduction body α 2 Gamma _
    (fun i => emb (Fin.cases a (fun _ => b) i))
  rw [matrixWitness]
  obtain ⟨hi⟩ := hi
  obtain ⟨hs⟩ := hs
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction hi hs) hb⟩

theorem successorStepIntroduction {body : Positive (Fin 1)} {n : Nat} {α : Type}
    (Gamma : List (Formula α)) (f : OFormula (Fin (n+1))) (g : OFormula (Fin (n+3)))
    (out t v : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α)
    (hr : Nonempty (Derivation body Gamma (recursion f g v t xs)))
    (hg : Nonempty (Derivation body Gamma (graph g out (Fin.cons t (Fin.cons v xs))))) :
    Nonempty (Derivation body Gamma (successorStep f g out t xs)) := by
  obtain ⟨hr⟩ := hr
  obtain ⟨hg⟩ := hg
  unfold successorStep
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb v)
  rw [successorStepInstantiate]
  exact Derivation.conjunctionIntroduction hr hg

theorem actualOriginalRecursionSuccessorElimination :
    InternalRecursionGraphTargets.ActualOriginalRecursionSuccessorElimination := by
  intro body n α f g out t xs
  let Gamma := [recursion f g out (suc t) xs]
  have h : Nonempty (Derivation body Gamma (successorStep f g out t xs)) := by
    apply recursionCases Gamma f g out (suc t) xs _ ⟨Derivation.hypothesis List.mem_cons_self⟩
    intro β j a b Delta _ hi hs hb
    rw [successorStepRename]
    simp only [sucRelabel] at hs hb
    obtain ⟨total⟩ := actualBetaTotality body β a b (t.relabel j)
    apply remainderCases Delta a b (t.relabel j) _ ⟨weakenClosed total Delta⟩
    intro γ l Theta v hl hv
    rw [successorStepRename]
    have hi' := renameInto hi l Theta hl
    rw [initialRename] at hi'
    have hs' := renameInto hs l Theta hl
    rw [stepRename,sucRelabel] at hs'
    have hb' := renameInto hb l Theta hl
    rw [betaRename,sucRelabel] at hb'
    have restrict := stepRestriction Theta g (a.relabel l) (b.relabel l)
      ((t.relabel j).relabel l) (fun i => ((xs i).relabel j).relabel l) hs'
    have hr := recursionIntroduction Theta f g (a.relabel l) (b.relabel l) v
      ((t.relabel j).relabel l) (fun i => ((xs i).relabel j).relabel l) hi' restrict hv
    have hg := stepElimination Theta g (a.relabel l) (b.relabel l)
      (suc ((t.relabel j).relabel l)) ((t.relabel j).relabel l) v ((out.relabel j).relabel l)
      (fun i => ((xs i).relabel j).relabel l) hs' ⟨equalToNext (refl _)⟩ hv hb'
    exact successorStepIntroduction Theta f g ((out.relabel j).relabel l)
      ((t.relabel j).relabel l) v (fun i => ((xs i).relabel j).relabel l) hr hg
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSuccessorEliminationProof
