module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBaseSemanticProof
public import LogicLineages.OrdinalComparison.WWSourceForwardTranslationProof
public import LogicLineages.OrdinalComparison.WWSourceAssignmentProfileProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBaseProof
open FiniteCoefficientBase Source Source.ForwardTranslation CommonLayerSyntax SourceClasses

private theorem extracted_coefficient (Γ : List Ty) (e : OrdinalExpression Γ) :
    ∀ c, extractPositive e = some c → noOmega e = true → ∃ k, coefficient c = some k := by
  induction e with
  | var _ | zero | collapse _ _ _ _ => intro c hc hn; simp [extractPositive] at hc
  | omega => intro c hc hn; simp [noOmega] at hn
  | one => intro c hc hn; cases Option.some.inj hc; exact ⟨1, rfl⟩
  | add a b iha ihb =>
    intro c hc hn
    obtain ⟨x, hx, y, hy, rfl⟩ : ∃ x, extractPositive a = some x ∧ ∃ y, extractPositive b = some y ∧ ClosedPositive.add x y=c := by
      simpa only [extractPositive, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hc
    have hab : noOmega a = true ∧ noOmega b = true := by simpa [noOmega] using hn
    obtain ⟨k, hk⟩ := iha x hx hab.1
    obtain ⟨l, hl⟩ := ihb y hy hab.2
    exact ⟨k+l, by simp [coefficient, hk, hl]⟩
  | emul a b iha ihb =>
    intro c hc hn
    obtain ⟨x, hx, y, hy, rfl⟩ : ∃ x, extractPositive a = some x ∧ ∃ y, extractPositive b = some y ∧ ClosedPositive.emul x y=c := by
      simpa only [extractPositive, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hc
    have hab : noOmega a = true ∧ noOmega b = true := by simpa [noOmega] using hn
    obtain ⟨k, hk⟩ := iha x hx hab.1
    obtain ⟨l, hl⟩ := ihb y hy hab.2
    exact ⟨2^k*l, by simp [coefficient, hk, hl]⟩

theorem noOmegaSource : FiniteCoefficientBaseTargets.NoOmegaSource := by
  intro Γ e
  induction e with
  | zero | omega | emul _ _ _ _ => intro s hs hn index; simp [compileScalar] at hs
  | one => intro s hs hn index; cases Option.some.inj hs; exact ⟨.numeral 1, rfl⟩
  | var i => intro s hs hn index; cases Option.some.inj hs; exact ⟨.variable (index i), rfl⟩
  | add a b iha ihb =>
    intro s hs hn index
    obtain ⟨x, hx, y, hy, rfl⟩ : ∃ x, compileScalar a = some x ∧ ∃ y, compileScalar b = some y ∧ Scalar.add x y=s := by
      simpa only [compileScalar, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hs
    have hab : noOmega a = true ∧ noOmega b = true := by simpa [noOmega] using hn
    obtain ⟨u, hu⟩ := iha x hx hab.1 index
    obtain ⟨v, hv⟩ := ihb y hy hab.2 index
    exact ⟨.add u v, by simp [compile, hu, hv]⟩
  | collapse a b iha ihb =>
    intro s hs hn index
    obtain ⟨c, hc, x, hx, rfl⟩ : ∃ c, extractPositive a = some c ∧ ∃ x, compileScalar b = some x ∧ Scalar.shift c x=s := by
      simpa only [compileScalar, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hs
    have hab : noOmega a = true ∧ noOmega b = true := by simpa [noOmega] using hn
    obtain ⟨k, hk⟩ := extracted_coefficient Γ a c hc hab.1
    obtain ⟨t, ht⟩ := ihb x hx hab.2 index
    exact ⟨expand k t, by simp [compile, hk, ht]⟩

theorem actualRecursorFreeSource : FiniteCoefficientBaseTargets.ActualRecursorFreeSource := by
  intro Γ hΓ τ e he
  obtain ⟨v, hv, hp, s, hs, hsem, hpos⟩ :=
    actualSourceForwardTranslation.2.2 Γ hΓ τ OrdinalSyntax.defaultPolicy e
  obtain ⟨w, hw, hn⟩ := actualRecursorFreeAssignmentNoOmega Γ τ OrdinalSyntax.defaultPolicy e he
  have hsame : w = v := Option.some.inj (hw.symm.trans hv)
  subst w
  obtain ⟨t, ht⟩ := noOmegaSource Γ (v 0) s hs (hn 0) rawIndex
  refine ⟨v, s, t, hv, hs, ht, ?_⟩
  intro ν
  rw [(actualScalar _ rawIndex s t ht).1 ν]
  exact hsem (fun c => ν (rawIndex c))

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBaseProof
