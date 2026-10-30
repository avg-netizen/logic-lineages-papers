module
public import LogicLineages.OrdinalComparison.WWGeneratedGradeTargets
public import LogicLineages.OrdinalComparison.WWTypedPartialProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open GeneratedOrdinalGrade

theorem actualGeneratedGradeRenaming : Targets.ActualGeneratedGradeRenaming := by
  intro Γ Δ ρ i t h
  induction h with
  | one i => exact .one i
  | omega i hi => exact .omega i hi
  | var v i => exact .var (ρ v) i
  | add _ _ hf hg => exact .add hf hg
  | emul hi _ _ hf hg => exact .emul hi hf hg
  | collapse _ _ hf hg => exact .collapse hf hg

theorem actualGeneratedGradeHeadClosure : Targets.ActualGeneratedGradeHeadClosure := by
  intro Γ σ i t h
  induction h with
  | one i => exact .one i
  | omega i hi => exact .omega i hi
  | var v i =>
    cases v with
    | here => exact .one i.val
    | there v => exact .var v i
  | add _ _ hf hg => exact .add hf hg
  | emul hi _ _ hf hg => exact .emul hi hf hg
  | collapse _ _ hf hg => exact .collapse hf hg

private theorem free_partial_graded {Γ : List Ty} {σ : Ty} {i : Nat}
    {t : OrdinalExpression (σ :: Γ)} (hg : GeneratedOrdinalGrade (σ :: Γ) i t)
    (hf : ordinalHeadFree t = true) : ∃ v : OrdinalPartialVector Γ σ,
      ordinalTypedPartial i t = some v ∧ ∀ j, GeneratedOrdinalGrade Γ j.val (v j) := by
  refine ⟨ordinalFreePartialVector i t, actualTypedFreePartial Γ σ i t hf, ?_⟩
  intro j
  unfold ordinalFreePartialVector
  split
  · rename_i hij
    rw [← hij]
    exact .add (actualGeneratedGradeHeadClosure Γ σ i t hg) (.one i)
  · exact .one j.val

theorem actualGeneratedGradePartial : Targets.ActualGeneratedGradePartial := by
  intro Γ σ i t h
  induction h with
  | one i => exact free_partial_graded (.one i) rfl
  | omega i hi => exact free_partial_graded (.omega i hi) rfl
  | var v k =>
    cases v with
    | here =>
      refine ⟨fun _ => .one, ?_, fun j => .one j.val⟩
      rw [actualTypedVariablePartial]
      simp
    | there v => exact free_partial_graded (.var (.there v) k) rfl
  | @add i f g hf hg ihf ihg =>
    by_cases hfree : ordinalHeadFree (.add f g) = true
    · exact free_partial_graded (.add hf hg) hfree
    · obtain ⟨pf, hpf, gpf⟩ := ihf
      obtain ⟨pg, hpg, gpg⟩ := ihg
      refine ⟨fun j => .add (.add (pf j) (pg j)) .one, ?_, ?_⟩
      · rw [actualTypedSumPartial Γ σ i f g (Bool.eq_false_iff.mpr hfree), hpf, hpg]
        rfl
      · intro j
        exact .add (.add (gpf j) (gpg j)) (.one j.val)
  | @emul i f g hi hf hg ihf ihg =>
    by_cases hfree : ordinalHeadFree (.emul f g) = true
    · exact free_partial_graded (.emul hi hf hg) hfree
    · obtain ⟨pf, hpf, gpf⟩ := ihf
      obtain ⟨pg, hpg, gpg⟩ := ihg
      refine ⟨fun j => .add (.add (.add (pf j) (pf j)) (pg j)) .one, ?_, ?_⟩
      · rw [actualTypedExponentialPartial Γ σ i f g (Bool.eq_false_iff.mpr hfree), if_pos hi,
          hpf, hpg]
        rfl
      · intro j
        exact .add (.add (.add (gpf j) (gpf j)) (gpg j)) (.one j.val)
  | @collapse f g hf hg ihf ihg =>
    by_cases hfree : ordinalHeadFree (.collapse f g) = true
    · exact free_partial_graded (.collapse hf hg) hfree
    · obtain ⟨pf, hpf, gpf⟩ := ihf
      obtain ⟨pg, hpg, gpg⟩ := ihg
      refine ⟨fun j => if j.val = 0 then .collapse (ordinalHeadClosure f) (pg 0)
        else .add (pf j) (pg j), ?_, ?_⟩
      · rw [actualTypedCollapsePartial Γ σ 0 f g (Bool.eq_false_iff.mpr hfree), if_pos rfl,
          hpf, hpg]
        rfl
      · intro j
        dsimp only
        split
        · rename_i hj
          rw [hj]
          exact .collapse (actualGeneratedGradeHeadClosure Γ σ 1 f hf) (gpg 0)
        · exact .add (gpf j) (gpg j)

end LogicLineages.OrdinalComparison.Source
