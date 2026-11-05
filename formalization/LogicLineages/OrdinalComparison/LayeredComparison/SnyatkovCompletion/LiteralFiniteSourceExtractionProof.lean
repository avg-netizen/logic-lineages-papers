module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LiteralFiniteSourceTargets
public import LogicLineages.OrdinalComparison.WWClosedPositiveEvaluationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LiteralFiniteSourceProof
open LiteralFiniteSource Source Source.ForwardTranslation
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

private theorem extraction_geometry (Γ : List Ty) (e : OrdinalExpression Γ) :
    ∀ c, extractPositive e = some c →
      ordinalExpressionVariables e = [] ∧ collapseHeads e = [] := by
  induction e with
  | var _ | zero | collapse _ _ _ _ =>
    intro c hc
    simp [extractPositive] at hc
  | one | omega =>
    intro c hc
    exact ⟨rfl, rfl⟩
  | add a b iha ihb =>
    intro c hc
    obtain ⟨x, hx, y, hy, _⟩ : ∃ x, extractPositive a = some x ∧
        ∃ y, extractPositive b = some y ∧ ClosedPositive.add x y = c := by
      simpa only [extractPositive, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] using hc
    obtain ⟨ha, hca⟩ := iha x hx
    obtain ⟨hb, hcb⟩ := ihb y hy
    exact ⟨by simp [ordinalExpressionVariables, ha, hb],
      by simp [collapseHeads, hca, hcb]⟩
  | emul a b iha ihb =>
    intro c hc
    obtain ⟨x, hx, y, hy, _⟩ : ∃ x, extractPositive a = some x ∧
        ∃ y, extractPositive b = some y ∧ ClosedPositive.emul x y = c := by
      simpa only [extractPositive, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] using hc
    obtain ⟨ha, hca⟩ := iha x hx
    obtain ⟨hb, hcb⟩ := ihb y hy
    exact ⟨by simp [ordinalExpressionVariables, ha, hb],
      by simp [collapseHeads, hca, hcb]⟩

theorem closedCoefficientExtraction : LiteralFiniteSourceTargets.ClosedCoefficientExtraction := by
  intro Γ e c hc
  obtain ⟨hv, hh⟩ := extraction_geometry Γ e c hc
  exact ⟨hv, hh, closedPositiveEvaluationSound Γ e c hc⟩

private theorem finite_add {Γ : List Ty} (a b : OrdinalExpression Γ) :
    finiteCollapseCoefficients (.add a b) ↔
      finiteCollapseCoefficients a ∧ finiteCollapseCoefficients b := by
  constructor
  · intro h
    constructor
    · intro c hc
      exact h c (List.mem_append.mpr (Or.inl hc))
    · intro c hc
      exact h c (List.mem_append.mpr (Or.inr hc))
  · rintro ⟨ha, hb⟩ c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact ha c hc
    · exact hb c hc

theorem literalScalarCorrespondence : LiteralFiniteSourceTargets.LiteralScalarCorrespondence := by
  intro Γ e
  induction e with
  | zero | omega | emul _ _ _ _ =>
    intro s hs
    simp [compileScalar] at hs
  | one =>
    intro s hs
    cases Option.some.inj hs
    simp [finiteCollapseCoefficients, collapseHeads, SemanticFiniteScalar.finiteHeads]
  | var i =>
    intro s hs
    cases Option.some.inj hs
    simp [finiteCollapseCoefficients, collapseHeads, SemanticFiniteScalar.finiteHeads]
  | add a b iha ihb =>
    intro s hs
    obtain ⟨x, hx, y, hy, rfl⟩ : ∃ x, compileScalar a = some x ∧
        ∃ y, compileScalar b = some y ∧ Scalar.add x y = s := by
      simpa only [compileScalar, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] using hs
    rw [finite_add, iha x hx, ihb y hy]
    rfl
  | collapse a b iha ihb =>
    intro s hs
    obtain ⟨c, hc, x, hx, rfl⟩ : ∃ c, extractPositive a = some c ∧
        ∃ x, compileScalar b = some x ∧ Scalar.shift c x = s := by
      simpa only [compileScalar, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] using hs
    obtain ⟨hclosed, hheads, hvalue⟩ := closedCoefficientExtraction Γ a c hc
    have hfinite : (∀ ρ : OrdinalComponent Γ → Ordinal,
        denote ρ a < Ordinal.omega0) ↔ c.evaluate.1.repr < Ordinal.omega0 := by
      constructor
      · intro h
        rw [hvalue (fun _ => 0)]
        exact h (fun _ => 0)
      · intro h ρ
        rw [← hvalue ρ]
        exact h
    have hsplit : finiteCollapseCoefficients (.collapse a b) ↔
        (∀ ρ : OrdinalComponent Γ → Ordinal, denote ρ a < Ordinal.omega0) ∧
          finiteCollapseCoefficients b := by
      simp only [finiteCollapseCoefficients, collapseHeads, hheads, List.nil_append,
        List.mem_cons, forall_eq_or_imp, hclosed, true_and]
    rw [hsplit, hfinite, ihb x hx]
    rfl

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LiteralFiniteSourceProof
