module
public import LogicLineages.OrdinalComparison.WWSourceAssignmentProfileTargets
public import LogicLineages.OrdinalComparison.WWSourceMacroProfileProof
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentProof
public import LogicLineages.OrdinalComparison.SourceTypeSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceClasses
open AdmissibleSum AdmissibleAssignment

private theorem assignment_noOmega {Γ : List Ty} {τ : Ty} (p : Policy) (t : OriginalTerm Γ τ)
    (v : OrdinalVector Γ τ.level) (hv : assignment p t = some v) (ht : recursorFree t = true) :
    ∀ j, noOmega (v j) = true := by
  induction t with
  | var x =>
    have he : (fun j => .var ⟨_, x, j⟩) = v := Option.some.inj hv
    subst v
    intro j
    rfl
  | zeroC | succC | caseC _ =>
    have he : (fun _ => .one) = v := Option.some.inj hv
    subst v
    intro j
    rfl
  | recC σ => simp [recursorFree] at ht
  | @app Γ σ τ f a ihf iha =>
    have hp : recursorFree f = true ∧ recursorFree a = true := by simpa [recursorFree] using ht
    rw [assignment] at hv
    obtain ⟨vf, hf, va, ha, he⟩ : ∃ vf, assignment p f = some vf ∧
        ∃ va, assignment p a = some va ∧ application p vf va = v := by
      simpa only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hv
    subst v
    intro j
    exact sourceBoxNoOmega Γ _ _ p vf va (ihf vf hf hp.1) (iha va ha hp.2)
      ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ (Nat.le_max_right _ _))⟩
  | @lam Γ σ τ body ih =>
    rw [assignment] at hv
    obtain ⟨vb, hb, hv⟩ : ∃ vb, assignment p body = some vb ∧ abstraction p vb = some v := by
      exact Option.bind_eq_some_iff.mp hv
    exact sourceAbstractionNoOmega Γ σ τ.level p vb v hv (ih vb hb ht)
  | ranked s args ih => nomatch s

private theorem root_level {Γ : List Ty} {τ : Ty} {L : Nat} (t : OriginalTerm Γ τ)
    (h : InternalLevelBound L t) : τ.level ≤ L :=
  h τ (SourceTypeSupportProof.actualResultSupport _ _ Γ τ t)

private theorem assignment_height {Γ : List Ty} {τ : Ty} (p : Policy) (L : Nat) (t : OriginalTerm Γ τ)
    (v : OrdinalVector Γ τ.level) (hv : assignment p t = some v) (ht : InternalLevelBound L t) :
    ∀ j, headHeight (v j) ≤ L - j.val := by
  induction t with
  | var x =>
    have he : (fun j => .var ⟨_, x, j⟩) = v := Option.some.inj hv
    subst v
    intro j
    exact Nat.zero_le _
  | zeroC | succC | caseC _ =>
    have he : (fun _ => .one) = v := Option.some.inj hv
    subst v
    intro j
    exact Nat.zero_le _
  | recC σ =>
    have he : (fun j : Fin (σ.recType.level + 1) => if j.val = 0 then numeral p 2
      else if j.val = σ.level + 2 then .omega else .one) = v := Option.some.inj hv
    subst v
    intro j
    dsimp only
    split
    · exact repeated_height p .numeral 2 .one _ (Nat.zero_le _)
    · split <;> exact Nat.zero_le _
  | @app Γ σ τ f a ihf iha =>
    have hLf : InternalLevelBound L f := fun υ hυ =>
      ht υ (Finset.mem_union_right _ (Finset.mem_union_left _ hυ))
    have hLa : InternalLevelBound L a := fun υ hυ =>
      ht υ (Finset.mem_union_right _ (Finset.mem_union_right _ hυ))
    rw [assignment] at hv
    obtain ⟨vf, hf, va, ha, he⟩ : ∃ vf, assignment p f = some vf ∧
        ∃ va, assignment p a = some va ∧ application p vf va = v := by
      simpa only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hv
    subst v
    intro j
    exact sourceBoxHeadHeight Γ L _ _ (by simp only [Ty.level]; omega) (root_level f hLf)
      p vf va (ihf vf hf hLf) (iha va ha hLa)
      ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ (Nat.le_max_right _ _))⟩
  | @lam Γ σ τ body ih =>
    have hLb : InternalLevelBound L body := fun υ hυ => ht υ (Finset.mem_union_right _ hυ)
    rw [assignment] at hv
    obtain ⟨vb, hb, hv⟩ : ∃ vb, assignment p body = some vb ∧ abstraction p vb = some v := by
      exact Option.bind_eq_some_iff.mp hv
    exact sourceAbstractionHeadHeight Γ σ L τ.level p vb v hv (ih vb hb hLb)
  | ranked s args ih => nomatch s

theorem actualRecursorFreeAssignmentNoOmega : Targets.ActualRecursorFreeAssignmentNoOmega := by
  intro Γ τ p t ht
  obtain ⟨v, hv, _⟩ := actualAdmissibleAssignmentGenerated Γ τ p t
  exact ⟨v, hv, assignment_noOmega p t v hv ht⟩

theorem actualInternalLevelAssignmentHeight : Targets.ActualInternalLevelAssignmentHeight := by
  intro Γ τ p L t ht
  obtain ⟨v, hv, _⟩ := actualAdmissibleAssignmentGenerated Γ τ p t
  exact ⟨v, hv, assignment_height p L t v hv ht⟩

end LogicLineages.OrdinalComparison.Source.SourceClasses
