module
public import LogicLineages.OrdinalComparison.WWSourceScalarHeadProfileTargets
public import LogicLineages.OrdinalComparison.WWSourceAssignmentProfileProof
public import LogicLineages.OrdinalComparison.WWScalarTranslationProof
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceClasses
open ForwardTranslation AdmissibleSum AdmissibleAssignment

theorem extractedPositiveHeadProfile : Targets.ExtractedPositiveHeadProfile := by
  intro Γ t c hs
  induction t generalizing c with
  | var x => simp [extractPositive] at hs
  | zero => simp [extractPositive] at hs
  | collapse f g ihf ihg => simp [extractPositive] at hs
  | one => cases Option.some.inj hs; rfl
  | omega => cases Option.some.inj hs; rfl
  | add f g ihf ihg =>
    obtain ⟨a, ha, b, hb, he⟩ : ∃ a, extractPositive f = some a ∧
        ∃ b, extractPositive g = some b ∧ ClosedPositive.add a b = c := by
      simpa only [extractPositive, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hs
    subst c
    simp only [positiveHeadHeight, headHeight, ihf a ha, ihg b hb]
  | emul f g ihf ihg =>
    obtain ⟨a, ha, b, hb, he⟩ : ∃ a, extractPositive f = some a ∧
        ∃ b, extractPositive g = some b ∧ ClosedPositive.emul a b = c := by
      simpa only [extractPositive, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hs
    subst c
    simp only [positiveHeadHeight, headHeight, ihf a ha, ihg b hb]

theorem compiledScalarHeadProfile : Targets.CompiledScalarHeadProfile := by
  intro Γ t s L hs hh
  induction t generalizing s with
  | var x => cases Option.some.inj hs; simp [scalarHeads]
  | one => cases Option.some.inj hs; simp [scalarHeads]
  | zero => simp [compileScalar] at hs
  | omega => simp [compileScalar] at hs
  | emul f g ihf ihg => simp [compileScalar] at hs
  | add f g ihf ihg =>
    obtain ⟨a, ha, b, hb, he⟩ : ∃ a, compileScalar f = some a ∧
        ∃ b, compileScalar g = some b ∧ Scalar.add a b = s := by
      simpa only [compileScalar, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hs
    subst s
    have hp : headHeight f ≤ L ∧ headHeight g ≤ L := Nat.max_le.mp hh
    intro c hc
    rcases List.mem_append.mp hc with hca | hcb
    · exact ihf a ha hp.1 c hca
    · exact ihg b hb hp.2 c hcb
  | collapse f g ihf ihg =>
    obtain ⟨a, ha, b, hb, he⟩ : ∃ a, extractPositive f = some a ∧
        ∃ b, compileScalar g = some b ∧ Scalar.shift a b = s := by
      simpa only [compileScalar, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hs
    subst s
    have hp : headHeight f + 1 ≤ L ∧ headHeight g ≤ L := Nat.max_le.mp hh
    intro c hc
    rcases List.mem_cons.mp hc with he | hc
    · subst c
      rw [extractedPositiveHeadProfile Γ f a ha]
      exact hp.1
    · exact ihg b hb hp.2 c hc

theorem actualLevelTwoSourceHeadProfile : Targets.ActualLevelTwoSourceHeadProfile := by
  intro Γ hΓ τ p t ht
  obtain ⟨v, hv, hg⟩ := actualAdmissibleAssignmentGenerated Γ τ p t
  obtain ⟨w, hw, hh⟩ := actualInternalLevelAssignmentHeight Γ τ p 2 t ht
  have he : w = v := Option.some.inj (hw.symm.trans hv)
  subst w
  obtain ⟨s, hs⟩ := generatedGroundScalarTranslationTotal Γ hΓ (v 0) (hg 0)
  refine ⟨v, hv, s, hs, fun c hc => ?_⟩
  have hb := compiledScalarHeadProfile Γ (v 0) s 2 hs (hh 0) c hc
  omega
end LogicLineages.OrdinalComparison.Source.SourceClasses
