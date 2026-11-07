module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphExtensionSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSuccessorIntroductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalRecursionGraph
open InternalRecursionGraphSyntaxProof InternalRecursionGraphStepSyntaxProof InternalRecursionGraphZeroEliminationProof
open InternalRecursionGraphSuccessorEliminationProof InternalRecursionGraphExtensionSupportProof
open InternalGraphCompositionSyntaxProof InternalClosedProgramsBindingProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalQuotientComparisonProof
open InternalBetaDivisionSyntaxProof InternalBetaTotalityProof InternalPositiveUnfoldingSupportProof

/-- Rebuild the literal universal step test, splitting the last index only
inside the original object calculus. -/
theorem stepExtension {body : Positive (Fin 1)} {n : Nat} {α : Type}
    (Gamma : List (Formula α)) (g : OFormula (Fin (n+3)))
    (a b c d out t old : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α)
    (hs : Nonempty (Derivation body Gamma (step g a b t xs)))
    (hp : Nonempty (Derivation body Gamma (InternalBetaExtension.sameBelow a b c d (suc t))))
    (hold : Nonempty (Derivation body Gamma (beta a b t old)))
    (hend : Nonempty (Derivation body Gamma (beta c d (suc t) out)))
    (hg : Nonempty (Derivation body Gamma (graph g out (Fin.cons t (Fin.cons old xs))))) :
    Nonempty (Derivation body Gamma (step g c d (suc t) xs)) := by
  rw [stepAsBlock]
  apply actualFiniteUniversalIntroduction body α 3 Gamma
  simp only [stepBody,sucRelabel]
  let j : OrdinaryArithmetic.Term (α ⊕ Fin 3) := .var (.inr 0)
  let v : OrdinaryArithmetic.Term (α ⊕ Fin 3) := .var (.inr 1)
  let w : OrdinaryArithmetic.Term (α ⊕ Fin 3) := .var (.inr 2)
  let A := a.relabel (Sum.inl : α → α ⊕ Fin 3)
  let B := b.relabel (Sum.inl : α → α ⊕ Fin 3)
  let C := c.relabel (Sum.inl : α → α ⊕ Fin 3)
  let D := d.relabel (Sum.inl : α → α ⊕ Fin 3)
  let O := out.relabel (Sum.inl : α → α ⊕ Fin 3)
  let T := t.relabel (Sum.inl : α → α ⊕ Fin 3)
  let V := old.relabel (Sum.inl : α → α ⊕ Fin 3)
  let XS := fun i => (xs i).relabel (Sum.inl : α → α ⊕ Fin 3)
  let P := (ltF j (suc T) ⊓ beta C D j v) ⊓ beta C D (suc j) w
  let Delta := P :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 3))
  let psi := graph g w (Fin.cons j (Fin.cons v XS))
  have inclusion : ∀ p ∈ Gamma, p.relabel (Sum.inl : α → α ⊕ Fin 3) ∈ Delta :=
    fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have hs' := renameInto hs Sum.inl Delta inclusion
  rw [stepRename] at hs'
  have hp' := renameInto hp Sum.inl Delta inclusion
  rw [InternalBetaExtensionSyntaxProof.sameBelowRename,sucRelabel] at hp'
  have hold' := renameInto hold Sum.inl Delta inclusion
  rw [betaRename] at hold'
  have hend' := renameInto hend Sum.inl Delta inclusion
  rw [betaRename,sucRelabel] at hend'
  have hg' := renameInto hg Sum.inl Delta inclusion
  simp only [graphRename,consTermRename] at hg'
  obtain ⟨hs'⟩ := hs'
  obtain ⟨hp'⟩ := hp'
  obtain ⟨hold'⟩ := hold'
  obtain ⟨hend'⟩ := hend'
  obtain ⟨hg'⟩ := hg'
  have dv : Derivation body Delta (beta C D j v) :=
    Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self))
  have dw : Derivation body Delta (beta C D (suc j) w) :=
    Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)
  have current : Derivation body Delta (beta C D T V) :=
    prefixForward A B C D (suc T) T V hp' (equalToNext (refl T)) hold'
  obtain ⟨split⟩ := InternalLeastNumberProof.actualRightSuccessorSplit body (α ⊕ Fin 3) j T
  rw [onEquality] at split
  have splitCases : Derivation body Delta (ltF j T ⊔ eqn j T) :=
    Derivation.implicationElimination (weakenClosed split Delta)
      (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)))
  have left : Nonempty (Derivation body Delta ((ltF j T).imp psi)) := by
    obtain ⟨res⟩ := oldStepBranch ((ltF j T) :: Delta) g A B C D T j v w XS
      ⟨addHyp hs' _⟩ ⟨addHyp hp' _⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
      ⟨addHyp dv _⟩ ⟨addHyp dw _⟩
    exact ⟨Derivation.implicationIntroduction res⟩
  have right : Nonempty (Derivation body Delta ((eqn j T).imp psi)) := by
    obtain ⟨res⟩ := boundaryStepBranch ((eqn j T) :: Delta) g C D O T V j v w XS
      ⟨addHyp current _⟩ ⟨addHyp hend' _⟩ ⟨addHyp hg' _⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp dv _⟩ ⟨addHyp dw _⟩
    exact ⟨Derivation.implicationIntroduction res⟩
  obtain ⟨left⟩ := left
  obtain ⟨right⟩ := right
  exact ⟨Derivation.implicationIntroduction (disjunctionElimination splitCases left right)⟩

/-- A direct consumer of literal prefix extension at succ(t), not t. -/
theorem recursionSuccessorIntroduction {body : Positive (Fin 1)} {n : Nat} {α : Type}
    (Gamma : List (Formula α)) (f : OFormula (Fin (n+1))) (g : OFormula (Fin (n+3)))
    (out t old : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α)
    (hr : Nonempty (Derivation body Gamma (recursion f g old t xs)))
    (hg : Nonempty (Derivation body Gamma (graph g out (Fin.cons t (Fin.cons old xs))))) :
    Nonempty (Derivation body Gamma (recursion f g out (suc t) xs)) := by
  apply recursionCases Gamma f g old t xs _ hr
  intro β j a b Delta hj hi hs hb
  rw [recursionRename,sucRelabel]
  have hg' := renameInto hg j Delta hj
  simp only [graphRename,consTermRename] at hg'
  obtain ⟨ext⟩ := InternalBetaExtensionProof.actualBetaSequenceExtension body β a b
    (suc (t.relabel j)) (out.relabel j)
  apply InternalBetaExtensionConsumerProof.extensionCases Delta a b (suc (t.relabel j))
    (out.relabel j) _ ⟨weakenClosed ext Delta⟩
  intro γ l Theta c d hl he
  rw [recursionRename,sucRelabel]
  have hi' := renameInto hi l Theta hl
  rw [initialRename] at hi'
  have hs' := renameInto hs l Theta hl
  rw [stepRename] at hs'
  have hb' := renameInto hb l Theta hl
  rw [betaRename] at hb'
  have hg'' := renameInto hg' l Theta hl
  simp only [graphRename,consTermRename] at hg''
  obtain ⟨he⟩ := he
  have hp : Nonempty (Derivation body Theta (InternalBetaExtension.sameBelow
      (a.relabel l) (b.relabel l) c d (suc ((t.relabel j).relabel l)))) := by
    have h := Derivation.conjunctionLeft he
    simpa only [sucRelabel] using (Nonempty.intro h)
  have hend : Nonempty (Derivation body Theta (beta c d (suc ((t.relabel j).relabel l))
      ((out.relabel j).relabel l))) := by
    have h := Derivation.conjunctionRight he
    simpa only [sucRelabel] using (Nonempty.intro h)
  have initialNew := initialTransfer Theta f (a.relabel l) (b.relabel l) c d
    ((t.relabel j).relabel l) (fun i => ((xs i).relabel j).relabel l) hi' hp
  have stepNew := stepExtension Theta g (a.relabel l) (b.relabel l) c d ((out.relabel j).relabel l)
    ((t.relabel j).relabel l) ((old.relabel j).relabel l)
    (fun i => ((xs i).relabel j).relabel l) hs' hp hb' hend hg''
  exact recursionIntroduction Theta f g c d ((out.relabel j).relabel l)
    (suc ((t.relabel j).relabel l)) (fun i => ((xs i).relabel j).relabel l) initialNew stepNew hend

/-- Expose the exact predecessor witness from the defining right-hand side. -/
theorem successorStepCases {body : Positive (Fin 1)} {n : Nat} {α : Type}
    (Gamma : List (Formula α)) (f : OFormula (Fin (n+1))) (g : OFormula (Fin (n+3)))
    (out t : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (successorStep f g out t xs)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (v : OrdinaryArithmetic.Term β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (recursion f g v (t.relabel j) (fun i => (xs i).relabel j))) →
      Nonempty (Derivation body Delta (graph g (out.relabel j)
        (Fin.cons (t.relabel j) (Fin.cons v (fun i => (xs i).relabel j))))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  let v : OrdinaryArithmetic.Term (α ⊕ Fin 1) := .var (.inr 0)
  let P := recursion f g v (t.relabel Sum.inl) (fun i => (xs i).relabel Sum.inl) ⊓
    graph g (out.relabel Sum.inl) (Fin.cons (t.relabel Sum.inl)
      (Fin.cons v (fun i => (xs i).relabel Sum.inl)))
  let Delta := P :: Gamma.map weaken
  have branch := k (α ⊕ Fin 1) Sum.inl Delta v
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  obtain ⟨branch⟩ := branch
  exact ⟨Derivation.existentialElimination h branch⟩

theorem actualOriginalRecursionSuccessorIntroduction :
    InternalRecursionGraphTargets.ActualOriginalRecursionSuccessorIntroduction := by
  intro body n α f g out t xs
  let Gamma := [successorStep f g out t xs]
  have h : Nonempty (Derivation body Gamma (recursion f g out (suc t) xs)) := by
    apply successorStepCases Gamma f g out t xs _ ⟨Derivation.hypothesis List.mem_cons_self⟩
    intro β j Delta v _ hr hg
    rw [recursionRename,sucRelabel]
    exact recursionSuccessorIntroduction Delta f g (out.relabel j) (t.relabel j) v
      (fun i => (xs i).relabel j) hr hg
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSuccessorIntroductionProof
