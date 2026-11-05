module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.RecursorFreeVectorTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBaseSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBaseCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedClosureDecisionSemanticProof
public import LogicLineages.OrdinalComparison.WWGroundPositiveQuerySplitProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.RecursorFreeVectorProof
open RecursorFreeVector Source Source.ForwardTranslation CommonLayerSyntax

 theorem scalar_formula (mode : Nat) (a b : BaseTerm) (ν : Nat → Nat) :
    (scalarFormula mode a b).eval ν ↔ scalarRelation mode (a.value ν) (b.value ν) := by
  unfold scalarFormula scalarRelation
  split
  · simp [BaseFormula.Formula.eval]
  · split <;> rfl

theorem exactFormula : RecursorFreeVectorTargets.ExactFormula := by
  classical
  intro n mode a b
  constructor
  · unfold Code.formula formula
    rw [BalancedClosureDecisionProof.literalGuardCode]
    unfold scalarFormula
    split <;> (try split) <;> rfl
  · intro ν
    have hg : (BalancedClosureDecision.positiveFormula (List.range n)).eval ν ↔
        ∀ i < n, 0 < ν i := by
      rw [BalancedClosureDecisionProof.exactPositiveGuard]
      simp only [List.mem_range]
    change (¬ (BalancedClosureDecision.positiveFormula (List.range n)).eval ν ∨
      (scalarFormula mode a b).eval ν) ↔ _
    rw [hg, scalar_formula]
    constructor
    · rintro (hn | hr) hp
      · exact False.elim (hn hp)
      · exact hr
    · intro h
      by_cases hp : ∀ i < n, 0 < ν i
      · exact Or.inr (h hp)
      · exact Or.inl hp

theorem positive_flag {ι : Type} {k l : Nat} (index : ι → Nat) (mode : Nat)
    (a : CompiledVector ι k) (b : CompiledVector ι l) :
    positiveFlag mode (a.syntaxCode index) (b.syntaxCode index) = true ↔
      (if mode = 0 then ∀ j, positiveNoteAt a.positiveNotes j ≤ positiveNoteAt b.positiveNotes j
       else if mode = 1 then ∀ j, positiveNoteAt a.positiveNotes j ≤ positiveNoteAt b.positiveNotes j
       else ∀ j, positiveNoteAt a.positiveNotes j = positiveNoteAt b.positiveNotes j) := by
  unfold positiveFlag
  rw [GroundPositiveQuerySplit.Proof.normalized_positive, GroundPositiveQuerySplit.Proof.normalized_positive]
  split
  · exact positiveComparisonSourceCorrect _ _
  · split
    · exact positiveComparisonSourceCorrect _ _
    · rw [Bool.and_eq_true, positiveComparisonSourceCorrect a.positiveNotes b.positiveNotes,
        positiveComparisonSourceCorrect b.positiveNotes a.positiveNotes]
      constructor
      · rintro ⟨hab,hba⟩ j
        exact le_antisymm (hab j) (hba j)
      · intro he
        exact ⟨fun j => (he j).le, fun j => (he j).ge⟩

theorem closed_answer (p : BaseFormula.Formula) : ∃ b,
    BaseBooleanSource.Code.decideClosureForall p.encode = some b ∧
      ((∀ ν, p.eval ν) ↔ b = true) := by
  classical
  by_cases h : ∀ ν, p.eval ν
  · exact ⟨true, ((BaseBooleanSourceProof.actualClosureDecisions p true).2).mpr (by simp [h]), by simp [h]⟩
  · exact ⟨false, ((BaseBooleanSourceProof.actualClosureDecisions p false).2).mpr (by simp [h]), by simp [h]⟩

theorem actualVectorDecision : RecursorFreeVectorTargets.ActualVectorDecision := by
  intro ι index n mode k l a b ta tb ha hb
  obtain ⟨answer,hd,hs⟩ := closed_answer (formula n mode ta tb)
  let flag := positiveFlag mode (a.syntaxCode index) (b.syntaxCode index)
  refine ⟨flag && answer, ?_, ?_⟩
  · unfold Code.decideVectors
    change (FiniteCoefficientBase.Code.compile (scalarSyntaxCode index a.scalar)).bind _ = _
    rw [FiniteCoefficientBaseProof.scalar_calibration, ha]
    simp only [Option.map_some, Option.bind_some]
    change (FiniteCoefficientBase.Code.compile (scalarSyntaxCode index b.scalar)).bind _ = _
    rw [FiniteCoefficientBaseProof.scalar_calibration, hb]
    simp only [Option.map_some, Option.bind_some]
    rw [(exactFormula n mode ta tb).1, hd]
    rfl
  · have hsem : (∀ ν : Nat → Nat, (∀ i < n, 0 < ν i) →
        scalarRelation mode (a.scalar.value (fun i => ν (index i))) (b.scalar.value (fun i => ν (index i)))) ↔
        answer = true := by
      rw [← hs]
      apply forall_congr'
      intro ν
      rw [(exactFormula n mode ta tb).2]
      rw [(FiniteCoefficientBaseProof.actualScalar ι index a.scalar ta ha).1 ν,
        (FiniteCoefficientBaseProof.actualScalar ι index b.scalar tb hb).1 ν]
    rw [Bool.and_eq_true, ← hsem]
    constructor
    · intro h
      have hpos := (h (fun _ => 1) (by intros; decide)).1
      exact ⟨(positive_flag index mode a b).mpr hpos, fun ν hp => (h ν hp).2⟩
    · rintro ⟨hf,hh⟩ ν hp
      exact ⟨(positive_flag index mode a b).mp hf, hh ν hp⟩

theorem actualSourceRelation : RecursorFreeVectorTargets.ActualSourceRelation := by
  intro Γ k l mode a b ca cb ha hb ρ
  have za : sourceVectorAtValue a ρ 0 = (ca.scalar.value ρ : Ordinal) := by
    simpa [sourceVectorAtValue, ordinalVectorAt, CompiledVector.value] using
      (compiledVectorSound Γ k a ca ha ρ 0).symm
  have zb : sourceVectorAtValue b ρ 0 = (cb.scalar.value ρ : Ordinal) := by
    simpa [sourceVectorAtValue, ordinalVectorAt, CompiledVector.value] using
      (compiledVectorSound Γ l b cb hb ρ 0).symm
  have hp (j : Nat) := GroundPositiveQuerySplit.Proof.positive_field a ca ha ρ j
  have hq (j : Nat) := GroundPositiveQuerySplit.Proof.positive_field b cb hb ρ j
  unfold vectorRelation sourceRelation scalarRelation
  split
  · simp only [SourceComparisonAt, Bool.false_eq_true, if_false, za, zb, Nat.cast_le, hp, hq]
  · split
    · simp only [SourceComparisonAt, if_true, za, zb, Nat.cast_lt, hp, hq]
    · constructor
      · rintro ⟨hpos,hzero⟩ j
        cases j with
        | zero => rw [za, zb, hzero]
        | succ j => simpa only [hp, hq] using hpos j
      · intro h
        refine ⟨fun j => ?_, ?_⟩
        · simpa only [hp, hq] using h (j+1)
        · simpa only [za, zb, Nat.cast_inj] using h 0
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.RecursorFreeVectorProof
