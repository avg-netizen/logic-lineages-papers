module
public import LogicLineages.OrdinalComparison.ScalarPartialActivityTargets
public import LogicLineages.OrdinalComparison.SourceAssignmentSupportPartialProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ScalarPartialActivity.Proof
open SourceFreeOccurrences AdmissibleSum AssignmentSupport AssignmentSupport.Proof

private theorem free_scalar_names {Γ σ} (p : Policy)
    (t : OrdinalExpression (σ :: Γ)) (v : OrdinalPartialVector Γ σ)
    (hf : ordinalHeadFree t = true) (hv : AdmissiblePartial.run p 0 t = some v) :
    names (v 0) = oldNames t := by
  rw [AdmissiblePartial.run.eq_def, if_pos hf] at hv
  cases hv
  simp [ordinalFreePartialVector, names_headClosure, oldNames]

theorem exactScalarOldNames : Targets.ExactScalarOldNames := by
  intro Γ σ p t
  induction t with
  | var c =>
    intro v hv x
    by_cases hf : ordinalHeadFree (.var c) = true
    · rw [free_scalar_names p _ v hf hv]
    · rcases c with ⟨τ, y, k⟩
      cases y with
      | here =>
        rw [AdmissiblePartial.run.eq_def, if_neg hf] at hv
        dsimp only at hv
        split at hv
        · cases hv
          simp [oldNames, componentName, dropBound]
        · cases hv
      | there y => simp [ordinalHeadFree, ordinalHeadOccurs, ordinalHeadComponentOccurs] at hf
  | zero =>
    intro v hv x
    rw [free_scalar_names p _ v (by rfl) hv]
  | one =>
    intro v hv x
    rw [free_scalar_names p _ v (by rfl) hv]
  | omega =>
    intro v hv x
    rw [free_scalar_names p _ v (by rfl) hv]
  | add f g ihf ihg =>
    intro v hv x
    by_cases hf : ordinalHeadFree (.add f g) = true
    · rw [free_scalar_names p _ v hf hv]
    · rw [AdmissiblePartial.run.eq_def, if_neg hf] at hv
      dsimp only at hv
      cases hpf : AdmissiblePartial.run p 0 f with
      | none => simp [hpf] at hv
      | some pf =>
        cases hpg : AdmissiblePartial.run p 0 g with
        | none => simp [hpf, hpg] at hv
        | some pg =>
          simp [hpf, hpg] at hv
          subst v
          simp only [names_three_mem, names_one, List.not_mem_nil, or_false]
          rw [ihf pf hpf x, ihg pg hpg x]
          simp only [oldNames, names_add, List.filterMap_append, List.mem_append]
  | emul f g ihf ihg =>
    intro v hv x
    by_cases hf : ordinalHeadFree (.emul f g) = true
    · rw [free_scalar_names p _ v hf hv]
    · rw [AdmissiblePartial.run.eq_def, if_neg hf] at hv
      simp at hv
  | collapse f g ihf ihg =>
    intro v hv x
    by_cases hf : ordinalHeadFree (.collapse f g) = true
    · rw [free_scalar_names p _ v hf hv]
    · rw [AdmissiblePartial.run.eq_def, if_neg hf] at hv
      dsimp only at hv
      cases hpf : AdmissiblePartial.run p 1 f with
      | none => simp [hpf] at hv
      | some pf =>
        cases hpg : AdmissiblePartial.run p 0 g with
        | none => simp [hpf, hpg] at hv
        | some pg =>
          simp [hpf, hpg] at hv
          subst v
          simp only [Fin.val_zero, ↓reduceIte, names_collapse, List.mem_append,
            names_headClosure]
          rw [ihg pg hpg x]
          simp only [oldNames, names_collapse, List.filterMap_append, List.mem_append]

end LogicLineages.OrdinalComparison.Source.ScalarPartialActivity.Proof
