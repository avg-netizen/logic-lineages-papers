module
public import LogicLineages.PermittedControl.SelectedGeneratedSourceTargets
public import LogicLineages.OrdinalComparison.WWClosedPositiveEvaluationProof
public import LogicLineages.OrdinalComparison.WWFiniteNaturalTailProof
public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedGeneratedSourceSoundProof
open OrdinalComparison Source Source.ForwardTranslation SelectedGeneratedSource
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

theorem closedSound : SelectedGeneratedSourceTargets.ClosedSound := by
  intro ctrl Γ t a hs
  induction t generalizing a with
  | var c => simp [extractPositive] at hs
  | zero => simp [extractPositive] at hs
  | one =>
    have he : ClosedPositive.one = a := Option.some.inj hs
    subst a
    intro ρ
    simp [ClosedPositive.evaluate, ParametricSourceSuccessor.denoteWith, ONote.repr_one]
  | omega =>
    have he : ClosedPositive.omega = a := Option.some.inj hs
    subst a
    intro ρ
    simp [ClosedPositive.evaluate, ParametricSourceSuccessor.denoteWith, ONote.repr]
  | add f g ihf ihg =>
    obtain ⟨x, hx, y, hy, he⟩ : ∃ x, extractPositive f = some x ∧
        ∃ y, extractPositive g = some y ∧ ClosedPositive.add x y = a := by
      simpa only [extractPositive, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hs
    subst a
    intro ρ
    change (naturalSum x.evaluate y.evaluate).1.repr = ordinalNaturalSum (ParametricSourceSuccessor.denoteWith ctrl ρ f) (ParametricSourceSuccessor.denoteWith ctrl ρ g)
    rw [naturalSumDenotation, ihf x hx ρ, ihg y hy ρ]
  | emul f g ihf ihg =>
    obtain ⟨x, hx, y, hy, he⟩ : ∃ x, extractPositive f = some x ∧
        ∃ y, extractPositive g = some y ∧ ClosedPositive.emul x y = a := by
      simpa only [extractPositive, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hs
    subst a
    intro ρ
    change (naturalProduct (NONote.opow ⟨ONote.ofNat 2, _⟩ x.evaluate) y.evaluate).1.repr =
      ordinalNaturalProduct ((2 : Ordinal) ^ ParametricSourceSuccessor.denoteWith ctrl ρ f) (ParametricSourceSuccessor.denoteWith ctrl ρ g)
    rw [naturalProductDenotation]
    change ordinalNaturalProduct ((ONote.ofNat 2) ^ x.evaluate.1).repr y.evaluate.1.repr = _
    letI : ONote.NF x.evaluate.1 := x.evaluate.2
    rw [ONote.repr_opow, ONote.repr_ofNat, ihf x hx ρ, ihg y hy ρ]
    rfl
  | collapse f g ihf ihg => simp [extractPositive] at hs

theorem scalarSound : SelectedGeneratedSourceTargets.ScalarSound := by
  intro ctrl Γ t s hs
  induction t generalizing s with
  | var c =>
    have he : Scalar.var c = s := Option.some.inj hs
    subst s
    intro ρ
    rfl
  | zero => simp [compileScalar] at hs
  | one =>
    have he : Scalar.one = s := Option.some.inj hs
    subst s
    intro ρ
    simp [scalarValueWith, ParametricSourceSuccessor.denoteWith]
  | omega => simp [compileScalar] at hs
  | add f g ihf ihg =>
    obtain ⟨a, ha, b, hb, he⟩ : ∃ a, compileScalar f = some a ∧
        ∃ b, compileScalar g = some b ∧ Scalar.add a b = s := by
      simpa only [compileScalar, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hs
    subst s
    intro ρ
    change ((scalarValueWith ctrl ρ a + scalarValueWith ctrl ρ b : Nat) : Ordinal) =
      ordinalNaturalSum (ParametricSourceSuccessor.denoteWith ctrl (fun c => (ρ c : Ordinal)) f) (ParametricSourceSuccessor.denoteWith ctrl (fun c => (ρ c : Ordinal)) g)
    rw [← ihf a ha ρ, ← ihg b hb ρ, naturalSum_finite]
  | emul f g ihf ihg => simp [compileScalar] at hs
  | collapse f g ihf ihg =>
    obtain ⟨a, ha, b, hb, he⟩ : ∃ a, extractPositive f = some a ∧
        ∃ b, compileScalar g = some b ∧ Scalar.shift a b = s := by
      simpa only [compileScalar, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hs
    subst s
    intro ρ
    change (ParametricActualCollapse.collapseWith ctrl (fixedHead a + (scalarValueWith ctrl ρ b : Ordinal)) : Ordinal) =
      (ParametricActualCollapse.collapseWith ctrl (ordinalNaturalSum
        (ordinalNaturalProduct Ordinal.omega0 (ParametricSourceSuccessor.denoteWith ctrl (fun c => (ρ c : Ordinal)) f))
        (ParametricSourceSuccessor.denoteWith ctrl (fun c => (ρ c : Ordinal)) g)) : Ordinal)
    rw [← closedSound ctrl Γ f a ha (fun c => (ρ c : Ordinal)),
      ← ihg b hb ρ, actualNaturalSumFiniteRight]
    rfl


end LogicLineages.PermittedControl.SelectedGeneratedSourceSoundProof
