module
public import LogicLineages.PermittedControl.SelectedHeadClosureTargets

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedHeadClosureProof
open OrdinalComparison Source SelectedSourceDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem headOneExtension : SelectedHeadClosureTargets.HeadOneExtension := by
  intro ctrl Γ σ ρ
  let v : {τ : Ty} → Variable (σ :: Γ) τ → Fin (τ.level + 1) → ClosedExpression :=
    fun {_} x j => match x with
      | .here => .one
      | .there y => ρ.vector y j
  have hg : ∀ {τ : Ty} (x : Variable (σ :: Γ) τ) (j : Fin (τ.level + 1)),
      ClosedGrade ctrl j.val (v x j) := by
    intro τ x j
    cases x with
    | here => exact .one j.val
    | there y => exact ρ.graded y j
  have hb : ∀ {τ : Ty} (x : Variable (σ :: Γ) τ) (j : Fin (τ.level + 1)),
      actualOrdinalNorm (closedValue ctrl (v x j)) ≤ actualOrdinalNorm (closedValue ctrl (v x 0)) := by
    intro τ x j
    cases x with
    | here => exact le_rfl
    | there y => exact ρ.bounded y j
  refine ⟨⟨v, hg, hb⟩, ?_, ?_⟩
  · intro j; rfl
  · intro τ x j; rfl

theorem headClosureValue : SelectedHeadClosureTargets.HeadClosureValue := by
  intro ctrl Γ σ ρ ρ' hh ho t
  induction t with
  | var c =>
    rcases c with ⟨τ, x, j⟩
    cases x with
    | here => simp [ordinalHeadClosure, substitute, ordinalHeadClosureComponent,
        expressionValue, ParametricSourceSuccessor.denoteWith, valuation, hh, closedValue]
    | there x => simp [ordinalHeadClosure, substitute, ordinalHeadClosureComponent,
        expressionValue, ParametricSourceSuccessor.denoteWith, valuation, ho]
  | zero => rfl
  | one => rfl
  | omega => rfl
  | add f g ihf ihg =>
    change ordinalNaturalSum (expressionValue ctrl ρ (ordinalHeadClosure f))
      (expressionValue ctrl ρ (ordinalHeadClosure g)) =
      ordinalNaturalSum (expressionValue ctrl ρ' f) (expressionValue ctrl ρ' g)
    rw [ihf, ihg]
  | emul f g ihf ihg =>
    change ordinalNaturalProduct ((2 : Ordinal) ^ expressionValue ctrl ρ (ordinalHeadClosure f))
      (expressionValue ctrl ρ (ordinalHeadClosure g)) =
      ordinalNaturalProduct ((2 : Ordinal) ^ expressionValue ctrl ρ' f) (expressionValue ctrl ρ' g)
    rw [ihf, ihg]
  | collapse f g ihf ihg =>
    change (ParametricActualCollapse.collapseWith ctrl (ordinalNaturalSum
      (ordinalNaturalProduct Ordinal.omega0 (expressionValue ctrl ρ (ordinalHeadClosure f)))
      (expressionValue ctrl ρ (ordinalHeadClosure g))) : Ordinal) =
      (ParametricActualCollapse.collapseWith ctrl (ordinalNaturalSum
      (ordinalNaturalProduct Ordinal.omega0 (expressionValue ctrl ρ' f))
      (expressionValue ctrl ρ' g)) : Ordinal)
    rw [ihf, ihg]

theorem headClosureNormPremise : SelectedHeadClosureTargets.HeadClosureNormPremise := by
  intro ctrl Γ σ f g hn ρ
  obtain ⟨ρ', hh, ho⟩ := headOneExtension ctrl Γ σ ρ
  rw [headClosureValue ctrl Γ σ ρ ρ' hh ho f,
    headClosureValue ctrl Γ σ ρ ρ' hh ho g]
  exact hn ρ'

theorem headClosureGrade : SelectedHeadClosureTargets.HeadClosureGrade := by
  intro ctrl Γ σ i t h
  induction h with
  | one i => exact .one i
  | omega i hi => exact .omega i hi
  | var x j =>
    cases x with
    | here => exact .one j.val
    | there y => exact .var y j
  | add hf hg ihf ihg => exact .add ihf ihg
  | emul hi hf hg ihf ihg => exact .emul hi ihf ihg
  | collapse hf hg hn ihf ihg =>
    exact .collapse ihf ihg (headClosureNormPremise ctrl _ _ _ _ hn)
  | promote hi hh hfree ih => exact .promote hi ih

theorem fullSelectedHeadClosure : SelectedHeadClosureTargets.FullSelectedHeadClosure :=
  ⟨headOneExtension,headClosureValue,headClosureNormPremise,headClosureGrade⟩

end LogicLineages.PermittedControl.SelectedHeadClosureProof
