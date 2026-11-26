module
public import LogicLineages.PermittedControl.SelectedValueClosureProof
public import LogicLineages.PermittedControl.CollapseProof
public import LogicLineages.OrdinalComparison.WWOriginalNormSumsProof
public import LogicLineages.OrdinalComparison.WWOriginalProductLowerProof
public import LogicLineages.OrdinalComparison.WWFiniteNaturalTailProof

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedGradedPositivityProof
open OrdinalComparison Source SelectedSourceDomain SelectedValueClosureProof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

theorem positive_of_norm {a : Ordinal} (h : 0 < actualOrdinalNorm a) : 0 < a := by
  by_contra hn
  have ha : a = 0 := le_antisymm (le_of_not_gt hn) zero_le
  have hz : actualOrdinalNorm 0 = 0 := by simpa using (finiteNorm 0).2
  rw [ha, hz] at h
  omega

theorem sum_positive {a b : Ordinal} (ha : 0 < a)
    (hae : a < epsilonZero) (hbe : b < epsilonZero) : 0 < ordinalNaturalSum a b := by
  apply positive_of_norm
  rw [Source.OriginalDomain.actualNaturalSumNormAdditivity a b hae hbe]
  have := Source.OriginalDomain.actualPositiveOrdinalNorm a ha hae
  omega

theorem product_positive {a b : Ordinal} (ha : 0 < a) (hb : 0 < b)
    (hae : a < epsilonZero) (hbe : b < epsilonZero) : 0 < ordinalNaturalProduct a b := by
  apply positive_of_norm
  have h := Source.OriginalDomain.actualNaturalProductNormLower a b ha hb hae hbe
  have hna := Source.OriginalDomain.actualPositiveOrdinalNorm a ha hae
  have hnb := Source.OriginalDomain.actualPositiveOrdinalNorm b hb hbe
  omega

theorem selected_forms {f : Nat → Nat} {B : Nat} (h : SelectedWithThreshold f B) :
    f = factorialControl ∨ ∃ b : Nat, f = nearControl b := by
  rcases h with ⟨h,_⟩ | ⟨b,h,_⟩
  · exact Or.inl h
  · exact Or.inr ⟨b,h⟩

theorem collapse_positive (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    {a b : Ordinal.{0}} (ha : a < epsilonZero) (hb : 0 < b)
    (hfin : ∃ n : Nat, b = (n : Ordinal.{0})) :
    0 < (ParametricActualCollapse.collapseWith f
      (ordinalNaturalSum (ordinalNaturalProduct Ordinal.omega0 a) b) : Ordinal.{0}) := by
  obtain ⟨n,rfl⟩ := hfin
  have hn : 0 < n := by exact_mod_cast hb
  rw [actualNaturalSumFiniteRight]
  have hc := (selectedCollapseEstimates f (selected_forms hf)).2.2.2.1
    (ordinalNaturalProduct Ordinal.omega0 a) n (product_below omega_below ha)
  have hn' : n ≤ ParametricActualCollapse.collapseWith f
      (ordinalNaturalProduct Ordinal.omega0 a + (n : Ordinal.{0})) :=
    (Nat.le_add_left n _).trans hc
  exact_mod_cast hn.trans_le hn'

theorem closed_positive (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    {i : Nat} {t : ClosedExpression} (ht : ClosedGrade f i t) : 0 < closedValue f t := by
  induction ht with
  | one i => exact zero_lt_one
  | omega i hi => exact Ordinal.omega0_pos
  | add ha hb iha ihb => exact sum_positive iha (closed_below f _) (closed_below f _)
  | emul hi ha hb iha ihb =>
    exact product_positive (Ordinal.opow_pos _ (by exact_mod_cast (show (0 : Nat) < 2 by omega))) ihb
      (two_power_below (closed_below f _)) (closed_below f _)
  | collapse ha hb hn iha ihb =>
    exact collapse_positive f B hf (closed_below f _) ihb
      (SourceScalarCalibrationProof.closed_scalar_finite f hb rfl)
  | promote hi hh ih => exact ih

theorem ambient_positive (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    {Γ : List Ty} {i : Nat} {t : OrdinalExpression Γ} (ht : AmbientGrade f Γ i t)
    (ρ : SelectedSourceDomain.AdmissibleSubstitution f Γ) : 0 < expressionValue f ρ t := by
  induction ht with
  | one i => exact zero_lt_one
  | omega i hi => exact Ordinal.omega0_pos
  | var x j => exact closed_positive f B hf (ρ.graded x j)
  | add ha hb iha ihb => exact sum_positive iha (ambient_below f ρ _) (ambient_below f ρ _)
  | emul hi ha hb iha ihb =>
    exact product_positive (Ordinal.opow_pos _ (by exact_mod_cast (show (0 : Nat) < 2 by omega))) ihb
      (two_power_below (ambient_below f ρ _)) (ambient_below f ρ _)
  | collapse ha hb hn iha ihb =>
    exact collapse_positive f B hf (ambient_below f ρ _) ihb
      (SourceScalarCalibrationProof.ambient_scalar_finite f hb ρ rfl)
  | promote hi hh ih => exact ih

theorem head_ambient (f : Nat → Nat) {Γ : List Ty} {σ : Ty} {i : Nat}
    {t : OrdinalExpression (σ :: Γ)} (h : HeadGrade f Γ σ i t) : AmbientGrade f (σ :: Γ) i t := by
  induction h with
  | one i => exact .one i
  | omega i hi => exact .omega i hi
  | var x j => exact .var x j
  | add ha hb iha ihb => exact .add iha ihb
  | emul hi ha hb iha ihb => exact .emul hi iha ihb
  | collapse ha hb hn iha ihb => exact .collapse iha ihb hn
  | promote hi hh hfree ih => exact .promote hi ih

theorem gradedPositivity : SelectedPositivityTargets.GradedPositivity := by
  intro f B hf
  exact ⟨fun _ _ ht => closed_positive f B hf ht,
    fun _ _ _ ht ρ => ambient_positive f B hf ht ρ,
    fun _ _ _ _ ht ρ => ambient_positive f B hf (head_ambient f ht) ρ⟩

theorem positiveScalars : SelectedPositivityTargets.PositiveScalars := by
  intro f B hf
  constructor
  · intro t ht
    obtain ⟨n,hn,hc,hN⟩ := SourceScalarCalibrationProof.scalarCalibration.2.1 f t ht
    have hp := closed_positive f B hf ht
    rw [hn] at hp
    exact ⟨n,by exact_mod_cast hp,hn,hc,hN⟩
  · intro Γ t ht ρ
    obtain ⟨n,hn,hc,hN⟩ := SourceScalarCalibrationProof.scalarCalibration.2.2 f Γ t ht ρ
    have hp := ambient_positive f B hf ht ρ
    rw [hn] at hp
    exact ⟨n,by exact_mod_cast hp,hn,hc,hN⟩

theorem fullSelectedPositivity : SelectedPositivityTargets.FullSelectedPositivity :=
  ⟨valueClosure,gradedPositivity,positiveScalars⟩

end LogicLineages.PermittedControl.SelectedGradedPositivityProof
