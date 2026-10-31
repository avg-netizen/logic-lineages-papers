module
public import LogicLineages.OrdinalComparison.WWCompiledVectorTargets
public import LogicLineages.OrdinalComparison.WWScalarTranslationProof
public import LogicLineages.OrdinalComparison.WWClosedPositiveEvaluationProof
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation
open AdmissibleAssignment

private theorem collect_success {α : Type} (n : Nat) (f : Fin n → Option α)
    (v : Fin n → α) (hv : collect n f = some v) : ∀ i, f i = some (v i) := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    have he : ∃ a, f 0 = some a ∧ ∃ w,
        collect n (fun i => f i.succ) = some w ∧ Fin.cases a w = v := by
      simpa only [collect, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hv
    obtain ⟨a, ha, w, hw, rfl⟩ := he
    intro i
    exact Fin.cases ha (ih _ w hw) i

private theorem collect_total {α : Type} (n : Nat) (f : Fin n → Option α)
    (hf : ∀ i, ∃ a, f i = some a) : ∃ v, collect n f = some v := by
  induction n with
  | zero => exact ⟨Fin.elim0, rfl⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := hf 0
    obtain ⟨w, hw⟩ := ih (fun i => f i.succ) (fun i => hf i.succ)
    exact ⟨Fin.cases a w, by simp [collect, ha, hw]⟩

theorem compiledVectorSound : Targets.CompiledVectorSound := by
  intro Γ n v c hc
  obtain ⟨s, hs, p, hp, he⟩ : ∃ s, compileScalar (v 0) = some s ∧
      ∃ p, collect n (fun j => extractPositive (v j.succ)) = some p ∧
        (CompiledVector.mk s p) = c := by
    simpa only [compileVector, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hc
  subst c
  intro ρ j
  refine Fin.cases ?_ (fun k => ?_) j
  · exact scalarTranslationSound Γ (v 0) s hs ρ
  · exact closedPositiveEvaluationSound Γ (v k.succ) (p k)
      (collect_success _ _ _ hp k) (fun x => (ρ x : Ordinal))

theorem generatedGroundVectorCompilationTotal : Targets.GeneratedGroundVectorCompilationTotal := by
  intro Γ hΓ n v hg
  obtain ⟨s, hs⟩ := generatedGroundScalarTranslationTotal Γ hΓ (v 0) (hg 0)
  obtain ⟨p, hp⟩ := collect_total n (fun j => extractPositive (v j.succ)) (fun j =>
    generatedClosedPositiveEvaluationTotal Γ j.succ.val (v j.succ) (hg j.succ) (Nat.succ_pos j.val)
      (actualGeneratedGroundPositiveClosed Γ hΓ j.succ.val (v j.succ) (Nat.succ_pos j.val) (hg j.succ)))
  exact ⟨⟨s, p⟩, by simp [compileVector, hs, hp]⟩

theorem actualSourceVectorCompilation : Targets.ActualSourceVectorCompilation := by
  intro Γ hΓ τ p t
  obtain ⟨v, hv, hg⟩ := actualAdmissibleAssignmentGenerated Γ τ p t
  obtain ⟨c, hc⟩ := generatedGroundVectorCompilationTotal Γ hΓ τ.level v hg
  exact ⟨v, hv, c, hc, compiledVectorSound Γ τ.level v c hc⟩
end LogicLineages.OrdinalComparison.Source.ForwardTranslation
