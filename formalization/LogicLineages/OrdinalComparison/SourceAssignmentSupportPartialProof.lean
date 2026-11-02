module
public import LogicLineages.OrdinalComparison.SourceAssignmentSupportStructureProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AssignmentSupport.Proof
open SourceFreeOccurrences AdmissibleSum

private theorem free_support {Γ σ} (p : Policy) (i : Nat)
    (t : OrdinalExpression (σ :: Γ)) (v : OrdinalPartialVector Γ σ)
    (hf : ordinalHeadFree t = true) (hv : AdmissiblePartial.run p i t = some v) :
    ∀ j, Supported ((names t).filterMap dropBound) (v j) := by
  rw [AdmissiblePartial.run.eq_def, if_pos hf] at hv
  cases hv
  intro j
  unfold ordinalFreePartialVector
  split <;> simp [Supported, names_headClosure]

private theorem append_support_left {Γ} {S T : List (PackedVariable Γ)}
    {t : OrdinalExpression Γ} (h : Supported S t) : Supported (S ++ T) t :=
  supported_mono (fun _ hx => List.mem_append_left _ hx) h

private theorem append_support_right {Γ} {S T : List (PackedVariable Γ)}
    {t : OrdinalExpression Γ} (h : Supported T t) : Supported (S ++ T) t :=
  supported_mono (fun _ hx => List.mem_append_right _ hx) h

theorem actualPartialSupport : Targets.ActualPartialSupport := by
  intro Γ σ p i t
  induction t generalizing i with
  | var c =>
    intro v hv
    by_cases hf : ordinalHeadFree (.var c) = true
    · exact free_support p i _ v hf hv
    · rcases c with ⟨τ, x, k⟩
      rw [AdmissiblePartial.run.eq_def, if_neg hf] at hv
      dsimp only at hv
      split at hv
      · cases hv
        simp [Supported]
      · cases hv
  | zero =>
    intro v hv
    exact free_support p i _ v (by rfl) hv
  | one =>
    intro v hv
    exact free_support p i _ v (by rfl) hv
  | omega =>
    intro v hv
    exact free_support p i _ v (by rfl) hv
  | add f g ihf ihg =>
    intro v hv
    by_cases hf : ordinalHeadFree (.add f g) = true
    · exact free_support p i _ v hf hv
    · rw [AdmissiblePartial.run.eq_def, if_neg hf] at hv
      dsimp only at hv
      cases hpf : AdmissiblePartial.run p i f with
      | none => simp [hpf] at hv
      | some pf =>
        cases hpg : AdmissiblePartial.run p i g with
        | none => simp [hpf, hpg] at hv
        | some pg =>
          simp [hpf, hpg] at hv
          subst v
          intro j
          simp only [names_add, List.filterMap_append]
          exact supported_three p .activeAdd (pf j) (pg j) .one
            (append_support_left (ihf i pf hpf j))
            (append_support_right (ihg i pg hpg j)) (by simp [Supported])
  | emul f g ihf ihg =>
    intro v hv
    by_cases hf : ordinalHeadFree (.emul f g) = true
    · exact free_support p i _ v hf hv
    · rw [AdmissiblePartial.run.eq_def, if_neg hf] at hv
      dsimp only at hv
      split at hv
      · cases hpf : AdmissiblePartial.run p (i + 1) f with
        | none => simp [hpf] at hv
        | some pf =>
          cases hpg : AdmissiblePartial.run p i g with
          | none => simp [hpf, hpg] at hv
          | some pg =>
            simp [hpf, hpg] at hv
            subst v
            intro j
            simp only [names_emul, List.filterMap_append]
            exact supported_three p .activeExp (AdmissiblePartial.twice p (pf j)) (pg j) .one
              (supported_twice p (pf j) (append_support_left (ihf (i + 1) pf hpf j)))
              (append_support_right (ihg i pg hpg j)) (by simp [Supported])
      · cases hv
  | collapse f g ihf ihg =>
    intro v hv
    by_cases hf : ordinalHeadFree (.collapse f g) = true
    · exact free_support p i _ v hf hv
    · rw [AdmissiblePartial.run.eq_def, if_neg hf] at hv
      dsimp only at hv
      split at hv
      · cases hpf : AdmissiblePartial.run p 1 f with
        | none => simp [hpf] at hv
        | some pf =>
          cases hpg : AdmissiblePartial.run p 0 g with
          | none => simp [hpf, hpg] at hv
          | some pg =>
            simp [hpf, hpg] at hv
            subst v
            intro j
            simp only [names_collapse, List.filterMap_append]
            split
            · intro x hx
              simp only [names_collapse, names_headClosure, List.mem_append] at hx
              rcases hx with hx | hx
              · exact List.mem_append_left _ hx
              · exact List.mem_append_right _ (ihg 0 pg hpg 0 x hx)
            · intro x hx
              simp only [names_add, List.mem_append] at hx
              rcases hx with hx | hx
              · exact List.mem_append_left _ (ihf 1 pf hpf j x hx)
              · exact List.mem_append_right _ (ihg 0 pg hpg j x hx)
      · cases hv

end LogicLineages.OrdinalComparison.Source.AssignmentSupport.Proof
