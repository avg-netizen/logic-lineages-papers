module
public import LogicLineages.PermittedControl.SelectedHardnessTargets
public import LogicLineages.PermittedControl.SelectedCanonicalDomainProof
public import LogicLineages.PermittedControl.SelectedGradedPositivityProof

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedHardnessCoordinatesProof
open OrdinalComparison Source Source.AdmissibleSum Source.AdmissibleAssignment
open SelectedSourceDomain SelectedHardness

theorem value0_of_assignment {Γ} (ctrl : Nat → Nat) (p : Policy)
    (ρ : AdmissibleSubstitution ctrl Γ) (a : OriginalTerm Γ unary)
    (v : OrdinalVector Γ 1) (n : Nat) (ha : assignment p a = some v)
    (hn : expressionValue ctrl ρ (v 0) = (n : Ordinal)) : value0 ctrl p ρ a = n := by
  unfold value0
  rw [ha]
  change finiteValue (expressionValue ctrl ρ (v 0)) = n
  rw [hn]
  exact (SourceScalarCalibrationProof.natural_calibration n).1

theorem value1_of_assignment {Γ} (ctrl : Nat → Nat) (p : Policy)
    (ρ : AdmissibleSubstitution ctrl Γ) (a : OriginalTerm Γ unary)
    (v : OrdinalVector Γ 1) (ha : assignment p a = some v) :
    value1 ctrl p ρ a = expressionValue ctrl ρ (v 1) := by
  unfold value1
  rw [ha]
  rfl

theorem coordinateFacts : SelectedHardnessTargets.CoordinateFacts := by
  intro ctrl K hc Γ p ρ a
  obtain ⟨v,ha,hcode,hgen,hgrade,hbound⟩ :=
    SelectedCanonicalDomainProof.canonicalAssignment ctrl K hc Γ unary p a
  obtain ⟨n,hp,hn,hfinite,hnorm⟩ :=
    (SelectedGradedPositivityProof.positiveScalars ctrl K hc).2 Γ (v 0) (hgrade 0) ρ
  have h0 := value0_of_assignment ctrl p ρ a v n ha hn
  have h1 := value1_of_assignment ctrl p ρ a v ha
  refine ⟨v,ha,?_,h1.symm,?_,?_,?_,?_⟩
  · rw [h0]; exact hn
  · rw [h0]; exact hp
  · rw [h1]
    exact SelectedGradedPositivityProof.ambient_positive ctrl K hc (hgrade 1) ρ
  · rw [h1]
    exact SelectedValueClosureProof.ambient_below ctrl ρ (v 1)
  · rw [h1,h0]
    have hb := (SelectedBoundedDeltaProof.boundedVectorSupportBridge ctrl Γ 1 v).mpr hbound ρ 1
    exact hb.trans (le_of_eq hnorm)

end LogicLineages.PermittedControl.SelectedHardnessCoordinatesProof
