module
public import LogicLineages.OrdinalComparison.WWClosedPositiveEvaluationTargets
public import LogicLineages.OrdinalComparison.NaturalProductInterpretation

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem closedPositiveEvaluationSound : Targets.ClosedPositiveEvaluationSound := by
  intro Γ t a hs
  induction t generalizing a with
  | var c => simp [extractPositive] at hs
  | zero => simp [extractPositive] at hs
  | one =>
    have he : ClosedPositive.one = a := Option.some.inj hs
    subst a
    intro ρ
    simp [ClosedPositive.evaluate, denote, ONote.repr_one]
  | omega =>
    have he : ClosedPositive.omega = a := Option.some.inj hs
    subst a
    intro ρ
    simp [ClosedPositive.evaluate, denote, ONote.repr]
  | add f g ihf ihg =>
    obtain ⟨x, hx, y, hy, he⟩ : ∃ x, extractPositive f = some x ∧
        ∃ y, extractPositive g = some y ∧ ClosedPositive.add x y = a := by
      simpa only [extractPositive, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hs
    subst a
    intro ρ
    change (naturalSum x.evaluate y.evaluate).1.repr = ordinalNaturalSum (denote ρ f) (denote ρ g)
    rw [naturalSumDenotation, ihf x hx ρ, ihg y hy ρ]
  | emul f g ihf ihg =>
    obtain ⟨x, hx, y, hy, he⟩ : ∃ x, extractPositive f = some x ∧
        ∃ y, extractPositive g = some y ∧ ClosedPositive.emul x y = a := by
      simpa only [extractPositive, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hs
    subst a
    intro ρ
    change (naturalProduct (NONote.opow ⟨ONote.ofNat 2, _⟩ x.evaluate) y.evaluate).1.repr =
      ordinalNaturalProduct ((2 : Ordinal) ^ denote ρ f) (denote ρ g)
    rw [naturalProductDenotation]
    change ordinalNaturalProduct ((ONote.ofNat 2) ^ x.evaluate.1).repr y.evaluate.1.repr = _
    letI : ONote.NF x.evaluate.1 := x.evaluate.2
    rw [ONote.repr_opow, ONote.repr_ofNat, ihf x hx ρ, ihg y hy ρ]
    rfl
  | collapse f g ihf ihg => simp [extractPositive] at hs

theorem generatedClosedPositiveEvaluationTotal : Targets.GeneratedClosedPositiveEvaluationTotal := by
  intro Γ i t hg
  induction hg with
  | one i => intro _ _; exact ⟨.one, rfl⟩
  | omega i hi => intro _ _; exact ⟨.omega, rfl⟩
  | var x j => intro _ hc; simp [ordinalExpressionVariables] at hc
  | add hf hg ihf ihg =>
    intro hi hc
    have hp : ordinalExpressionVariables _ = [] ∧ ordinalExpressionVariables _ = [] :=
      List.append_eq_nil_iff.mp hc
    obtain ⟨a, ha⟩ := ihf hi hp.1
    obtain ⟨b, hb⟩ := ihg hi hp.2
    exact ⟨.add a b, by simp [extractPositive, ha, hb]⟩
  | emul hi hf hg ihf ihg =>
    intro _ hc
    have hp : ordinalExpressionVariables _ = [] ∧ ordinalExpressionVariables _ = [] :=
      List.append_eq_nil_iff.mp hc
    obtain ⟨a, ha⟩ := ihf (by omega) hp.1
    obtain ⟨b, hb⟩ := ihg hi hp.2
    exact ⟨.emul a b, by simp [extractPositive, ha, hb]⟩
  | collapse hf hg ihf ihg => intro hi _; omega

end LogicLineages.OrdinalComparison.Source.ForwardTranslation
