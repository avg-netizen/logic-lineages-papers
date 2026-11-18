module
public import LogicLineages.PermittedControl.SourceFinitenessTargets
public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
public import LogicLineages.OrdinalComparison.ParametricActualCollapseProof

@[expose] public section
namespace LogicLineages.PermittedControl.SourceScalarCalibrationProof
open OrdinalComparison Source SelectedSourceDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

 theorem natural_calibration (n : Nat) : SelectedSourceDomain.finiteValue (n : Ordinal.{0}) = n ∧
    actualOrdinalNorm (n : Ordinal.{0}) = n := by
  refine ⟨?_,(ParametricActualCollapse.Proof.natural_facts n).2⟩
  simp [SelectedSourceDomain.finiteValue,Ordinal.card_nat]

 theorem closed_scalar_finite (ctrl : Nat → Nat) {i : Nat} {t : ClosedExpression}
    (h : ClosedGrade ctrl i t) : i = 0 → ∃ n : Nat, closedValue ctrl t = (n : Ordinal.{0}) := by
  induction h with
  | one i => intro _; exact ⟨1,by simp [closedValue, expressionValue, ParametricSourceSuccessor.denoteWith]⟩
  | omega i hi => intro he; omega
  | add hf hg ihf ihg =>
    intro he
    obtain ⟨a,ha⟩ := ihf he
    obtain ⟨b,hb⟩ := ihg he
    refine ⟨a+b,?_⟩
    change ordinalNaturalSum (closedValue ctrl _) (closedValue ctrl _) = _
    rw [ha,hb,naturalSum_finite]
  | emul hi hf hg ihf ihg => intro he; omega
  | collapse hf hg hn ihf ihg => intro _; exact ⟨_,rfl⟩
  | promote hi hh ih => intro he; omega

 theorem ambient_scalar_finite (ctrl : Nat → Nat) {Γ : List Ty} {i : Nat}
    {t : OrdinalExpression Γ} (h : AmbientGrade ctrl Γ i t)
    (ρ : SelectedSourceDomain.AdmissibleSubstitution ctrl Γ) :
    i=0 → ∃ n : Nat, expressionValue ctrl ρ t = (n : Ordinal.{0}) := by
  induction h with
  | one i => intro _; exact ⟨1,by simp [closedValue, expressionValue, ParametricSourceSuccessor.denoteWith]⟩
  | omega i hi => intro he; omega
  | var x j =>
    intro he
    have hj : j=0 := Fin.ext he
    subst j
    exact closed_scalar_finite ctrl (ρ.graded x 0) rfl
  | add hf hg ihf ihg =>
    intro he
    obtain ⟨a,ha⟩ := ihf he
    obtain ⟨b,hb⟩ := ihg he
    refine ⟨a+b,?_⟩
    change ordinalNaturalSum (expressionValue ctrl ρ _) (expressionValue ctrl ρ _) = _
    rw [ha,hb,naturalSum_finite]
  | emul hi hf hg ihf ihg => intro he; omega
  | collapse hf hg hn ihf ihg => intro _; exact ⟨_,rfl⟩
  | promote hi hh ih => intro he; omega

 theorem scalarCalibration : SourceFinitenessTargets.ScalarCalibration := by
  refine ⟨natural_calibration,?_,?_⟩
  · intro f t ht
    obtain ⟨n,hn⟩ := closed_scalar_finite f ht rfl
    exact ⟨n,hn,by rw [hn]; exact (natural_calibration n).1,
      by rw [hn]; exact (natural_calibration n).2⟩
  · intro f Γ t ht ρ
    obtain ⟨n,hn⟩ := ambient_scalar_finite f ht ρ rfl
    exact ⟨n,hn,by rw [hn]; exact (natural_calibration n).1,
      by rw [hn]; exact (natural_calibration n).2⟩

end LogicLineages.PermittedControl.SourceScalarCalibrationProof
