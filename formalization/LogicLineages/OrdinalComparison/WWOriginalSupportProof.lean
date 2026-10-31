module
public import LogicLineages.OrdinalComparison.WWOriginalSupportTargets
public import LogicLineages.OrdinalComparison.WWOriginalWeakPartialProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem originalSupportedExtension : Targets.OriginalSupportedExtension := by
  classical
  intro Γ S ρ
  let v : {τ : Ty} → Variable Γ τ → Fin (τ.level + 1) → ClosedExpression :=
    fun {τ} x j => if hx : S ⟨τ, x⟩ then ρ.vector x hx j else .one
  have hg : ∀ {τ : Ty} (x : Variable Γ τ) (j : Fin (τ.level + 1)),
      ClosedGrade j.val (v x j) := by
    intro τ x j
    dsimp only [v]
    split
    · rename_i hx
      exact ρ.graded x hx j
    · exact .one j.val
  have hb : ∀ {τ : Ty} (x : Variable Γ τ) (j : Fin (τ.level + 1)),
      actualOrdinalNorm (closedValue (v x j)) ≤ actualOrdinalNorm (closedValue (v x 0)) := by
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
  · simp [valuation, supportedValuation, componentName, v, hx, closedValue, denote]

theorem originalComparisonSupportCoverage : Targets.OriginalComparisonSupportCoverage := by
  intro Γ t u
  constructor
  · intro c hc
    exact ⟨c, Or.inl hc, rfl⟩
  · intro c hc
    exact ⟨c, Or.inr hc, rfl⟩

private def restrict {Γ : List Ty} (S : VariableName Γ → Prop)
    (ρ : AdmissibleSubstitution Γ) : SupportedSubstitution Γ S :=
  ⟨(fun {_} x _ j => ρ.vector x j),
    (fun {_} x _ j => ρ.graded x j), (fun {_} x _ j => ρ.bounded x j)⟩

private theorem restriction_value {Γ : List Ty} {S : VariableName Γ → Prop}
    (ρ : AdmissibleSubstitution Γ) (t : OrdinalExpression Γ) (ht : UsesOnly S t) :
    supportedValue (restrict S ρ) t = expressionValue ρ t := by
  induction t with
  | var c =>
    have hc := ht c (by simp [ordinalExpressionVariables])
    simp [supportedValue, expressionValue, denote, supportedValuation, hc, restrict, valuation]
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
    exact congrArg₂ (fun a b : Ordinal => (actualCollapse
      (ordinalNaturalSum (ordinalNaturalProduct Ordinal.omega0 a) b) : Ordinal))
      (ihf hf) (ihg hg)

theorem originalSupportComparisonBridge : Targets.OriginalSupportComparisonBridge := by
  intro Γ S t u ht hu P
  constructor
  · intro h ρ
    obtain ⟨ρ', he⟩ := originalSupportedExtension Γ S ρ
    have het : expressionValue ρ' t = supportedValue ρ t :=
      congrArg (fun v => denote v t) (funext he)
    have heu : expressionValue ρ' u = supportedValue ρ u :=
      congrArg (fun v => denote v u) (funext he)
    simpa only [het, heu] using h ρ'
  · intro h ρ
    have hr := h (restrict S ρ)
    simpa only [restriction_value ρ t ht, restriction_value ρ u hu] using hr

theorem originalSourceWeakScalar : Targets.OriginalSourceWeakScalar := by
  intro Γ σ p t ht
  obtain ⟨v, hv, gv, wv⟩ := originalPartialWeakAndValid Γ σ p 0 t ht
  refine ⟨v, hv, ?_⟩
  have hs := originalComparisonSupportCoverage Γ (ordinalHeadClosure t) (v 0)
  exact (originalSupportComparisonBridge Γ _ _ _ hs.1 hs.2 (· ≤ ·)).mp (wv rfl)

end LogicLineages.OrdinalComparison.Source.OriginalDomain
