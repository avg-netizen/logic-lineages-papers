module
public import LogicLineages.PermittedControl.SelectedWeakScalarTargets

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedSupportProof
open OrdinalComparison Source SelectedSourceDomain SelectedSourceSupport
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem supportedExtension : SelectedWeakScalarTargets.SupportedExtension := by
  classical
  intro ctrl Γ S ρ
  let v : {τ : Ty} → Variable Γ τ → Fin (τ.level + 1) → ClosedExpression :=
    fun {τ} x j => if hx : S ⟨τ, x⟩ then ρ.vector x hx j else .one
  have hg : ∀ {τ : Ty} (x : Variable Γ τ) (j : Fin (τ.level + 1)),
      ClosedGrade ctrl j.val (v x j) := by
    intro τ x j
    dsimp only [v]
    split
    · rename_i hx
      exact ρ.graded x hx j
    · exact .one j.val
  have hb : ∀ {τ : Ty} (x : Variable Γ τ) (j : Fin (τ.level + 1)),
      actualOrdinalNorm (closedValue ctrl (v x j)) ≤ actualOrdinalNorm (closedValue ctrl (v x 0)) := by
    intro τ x j
    dsimp only [v]
    split
    · rename_i hx
      exact ρ.bounded x hx j
    · exact le_rfl
  refine ⟨⟨v, hg, hb⟩, ?_⟩
  intro c
  rcases c with ⟨τ, x, j⟩
  by_cases hx : S ⟨τ, x⟩
  · simp [valuation, supportedValuation, componentName, v, hx]
  · simp [valuation, supportedValuation, componentName, v, hx, closedValue, ParametricSourceSuccessor.denoteWith]

theorem comparisonSupportCoverage : SelectedWeakScalarTargets.ComparisonSupportCoverage := by
  intro Γ t u
  constructor
  · intro c hc
    exact ⟨c, Or.inl hc, rfl⟩
  · intro c hc
    exact ⟨c, Or.inr hc, rfl⟩

private def restrict (ctrl : Nat → Nat) {Γ : List Ty} (S : VariableName Γ → Prop)
    (ρ : AdmissibleSubstitution ctrl Γ) : SupportedSubstitution ctrl Γ S :=
  ⟨(fun {_} x _ j => ρ.vector x j),
    (fun {_} x _ j => ρ.graded x j), (fun {_} x _ j => ρ.bounded x j)⟩

private theorem restriction_value (ctrl : Nat → Nat) {Γ : List Ty} {S : VariableName Γ → Prop}
    (ρ : AdmissibleSubstitution ctrl Γ) (t : OrdinalExpression Γ) (ht : UsesOnly S t) :
    supportedValue ctrl (restrict ctrl S ρ) t = expressionValue ctrl ρ t := by
  induction t with
  | var c =>
    have hc := ht c (by simp [ordinalExpressionVariables])
    simp [supportedValue, expressionValue, ParametricSourceSuccessor.denoteWith, supportedValuation, hc, restrict, valuation]
  | zero => rfl
  | one => rfl
  | omega => rfl
  | add f g ihf ihg =>
    have hf : UsesOnly S f := fun c hc => ht c (by simp [ordinalExpressionVariables, hc])
    have hg : UsesOnly S g := fun c hc => ht c (by simp [ordinalExpressionVariables, hc])
    exact congrArg₂ ordinalNaturalSum (ihf hf) (ihg hg)
  | emul f g ihf ihg =>
    have hf : UsesOnly S f := fun c hc => ht c (by simp [ordinalExpressionVariables, hc])
    have hg : UsesOnly S g := fun c hc => ht c (by simp [ordinalExpressionVariables, hc])
    exact congrArg₂ (fun a b : Ordinal => ordinalNaturalProduct ((2 : Ordinal) ^ a) b)
      (ihf hf) (ihg hg)
  | collapse f g ihf ihg =>
    have hf : UsesOnly S f := fun c hc => ht c (by simp [ordinalExpressionVariables, hc])
    have hg : UsesOnly S g := fun c hc => ht c (by simp [ordinalExpressionVariables, hc])
    exact congrArg₂ (fun a b : Ordinal => (ParametricActualCollapse.collapseWith ctrl
      (ordinalNaturalSum (ordinalNaturalProduct Ordinal.omega0 a) b) : Ordinal))
      (ihf hf) (ihg hg)

theorem supportComparisonBridge : SelectedWeakScalarTargets.SupportComparisonBridge := by
  intro ctrl Γ S t u ht hu P
  constructor
  · intro h ρ
    obtain ⟨ρ', he⟩ := supportedExtension ctrl Γ S ρ
    have het : expressionValue ctrl ρ' t = supportedValue ctrl ρ t :=
      congrArg (fun v => ParametricSourceSuccessor.denoteWith ctrl v t) (funext he)
    have heu : expressionValue ctrl ρ' u = supportedValue ctrl ρ u :=
      congrArg (fun v => ParametricSourceSuccessor.denoteWith ctrl v u) (funext he)
    simpa only [het, heu] using h ρ'
  · intro h ρ
    have hr := h (restrict ctrl S ρ)
    simpa only [restriction_value ctrl ρ t ht, restriction_value ctrl ρ u hu] using hr

theorem evaluationIndependence : SelectedWeakScalarTargets.EvaluationIndependence := by
  intro ctrl Γ t ρ τ h
  induction t with
  | var c => exact h c (by simp [ordinalExpressionVariables])
  | zero => rfl
  | one => rfl
  | omega => rfl
  | add a b iha ihb =>
    apply congrArg₂ ordinalNaturalSum
    · exact iha (fun c hc => h c (by simp [ordinalExpressionVariables,hc]))
    · exact ihb (fun c hc => h c (by simp [ordinalExpressionVariables,hc]))
  | emul a b iha ihb =>
    apply congrArg₂ (fun a b : Ordinal => ordinalNaturalProduct ((2 : Ordinal)^a) b)
    · exact iha (fun c hc => h c (by simp [ordinalExpressionVariables,hc]))
    · exact ihb (fun c hc => h c (by simp [ordinalExpressionVariables,hc]))
  | collapse a b iha ihb =>
    apply congrArg₂ (fun a b : Ordinal => (ParametricActualCollapse.collapseWith ctrl
      (ordinalNaturalSum (ordinalNaturalProduct Ordinal.omega0 a) b) : Ordinal))
    · exact iha (fun c hc => h c (by simp [ordinalExpressionVariables,hc]))
    · exact ihb (fun c hc => h c (by simp [ordinalExpressionVariables,hc]))

end LogicLineages.PermittedControl.SelectedSupportProof
