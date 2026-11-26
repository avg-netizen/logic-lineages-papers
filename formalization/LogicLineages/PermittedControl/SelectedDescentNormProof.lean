module
public import LogicLineages.PermittedControl.SelectedFirstFreeTargets
public import LogicLineages.PermittedControl.SelectedGradedPositivityProof
public import LogicLineages.OrdinalComparison.WWOriginalPowerNormProof

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedDescentNormProof
open OrdinalComparison Source SelectedSourceDomain SelectedValueClosureProof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

theorem addChildNorm : SelectedFirstFreeTargets.AddChildNorm := by
  intro ctrl K hctrl Γ ρ i f g hf hg
  have h := Source.OriginalDomain.actualNaturalSumNormAdditivity (expressionValue ctrl ρ f) (expressionValue ctrl ρ g)
    (SelectedValueClosureProof.ambient_below ctrl ρ f) (SelectedValueClosureProof.ambient_below ctrl ρ g)
  change actualOrdinalNorm (expressionValue ctrl ρ f) ≤ actualOrdinalNorm
    (ordinalNaturalSum (expressionValue ctrl ρ f) (expressionValue ctrl ρ g)) ∧
    actualOrdinalNorm (expressionValue ctrl ρ g) ≤ actualOrdinalNorm
    (ordinalNaturalSum (expressionValue ctrl ρ f) (expressionValue ctrl ρ g))
  rw [h]
  constructor <;> omega

theorem expChildNorm : SelectedFirstFreeTargets.ExpChildNorm := by
  intro ctrl K hctrl Γ ρ i f g hi hf hg
  have hfe := SelectedValueClosureProof.ambient_below ctrl ρ f
  have hge := SelectedValueClosureProof.ambient_below ctrl ρ g
  have hgp := SelectedGradedPositivityProof.ambient_positive ctrl K hctrl hg ρ
  have hpp : (0 : Ordinal) < (2 : Ordinal) ^ expressionValue ctrl ρ f :=
    Ordinal.opow_pos _ (by exact_mod_cast (show (0 : Nat) < 2 by omega))
  have hp := Source.OriginalDomain.actualNaturalProductComponentNorm _ _ hpp hgp (two_power_below hfe) hge
  have hi' := Source.OriginalDomain.actualBaseTwoInverseNorm (expressionValue ctrl ρ f) hfe
  exact ⟨hi'.trans (Nat.mul_le_mul_left 2 hp.1), hp.2⟩

theorem collapseChildNorm : SelectedFirstFreeTargets.CollapseChildNorm := by
  intro ctrl K hctrl Γ ρ f g hf hg
  let a := expressionValue ctrl ρ f
  let b := expressionValue ctrl ρ g
  let head := ordinalNaturalProduct Ordinal.omega0 a
  let arg := ordinalNaturalSum head b
  have hae : a < epsilonZero := SelectedValueClosureProof.ambient_below ctrl ρ f
  have hbe : b < epsilonZero := SelectedValueClosureProof.ambient_below ctrl ρ g
  have hap : 0 < a := SelectedGradedPositivityProof.ambient_positive ctrl K hctrl hf ρ
  have hω : Ordinal.omega0 < epsilonZero := SelectedValueClosureProof.omega_below
  have hhead : head < epsilonZero := product_below hω hae
  have harg : arg < epsilonZero := sum_below hhead hbe
  have hprod := (Source.OriginalDomain.actualNaturalProductComponentNorm Ordinal.omega0 a
    Ordinal.omega0_pos hap hω hae).2
  have hsum := Source.OriginalDomain.actualNaturalSumNormAdditivity head b hhead hbe
  have hcollapse := (selectedCollapseEstimates ctrl (SelectedGradedPositivityProof.selected_forms hctrl)).2.2.1 arg harg
  have hfinite := (finiteNorm (ParametricActualCollapse.collapseWith ctrl arg)).2
  change actualOrdinalNorm a ≤ actualOrdinalNorm (ParametricActualCollapse.collapseWith ctrl arg : Ordinal) ∧
    actualOrdinalNorm b ≤ actualOrdinalNorm (ParametricActualCollapse.collapseWith ctrl arg : Ordinal)
  rw [hfinite]
  change actualOrdinalNorm a ≤ actualOrdinalNorm head at hprod
  change actualOrdinalNorm arg = actualOrdinalNorm head + actualOrdinalNorm b at hsum
  constructor <;> omega

end LogicLineages.PermittedControl.SelectedDescentNormProof
