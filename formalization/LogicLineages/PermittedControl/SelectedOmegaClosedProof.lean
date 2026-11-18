module
public import LogicLineages.PermittedControl.SelectedOmegaSeedTargets
public import LogicLineages.PermittedControl.SelectedValueClosureProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.OmegaClosedProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedOmegaSeed.Proof
open OrdinalComparison Source SelectedSourceDomain
open Source.FunctionalHardnessCompletion

/-- Both literal expressions are collapse-free; the two interpretations reduce identically. -/
 theorem exponent_calibration (ctrl : Nat → Nat) : exponent ctrl=OmegaSeed.exponent := rfl
 theorem omega_calibration (ctrl : Nat → Nat) : omega ctrl=OmegaSeed.omega := rfl

 theorem omega_grade (ctrl : Nat → Nat) : ClosedGrade ctrl 1 OmegaSeed.omegaExpression := by
  have step_grade (i : Nat) (hi : 0 < i) (t : ClosedExpression) (ht : ClosedGrade ctrl i t) :
      ClosedGrade ctrl i (OmegaSeed.topStep t) :=
    .emul hi (.omega (i+1) (by omega)) (.add (.one i) (.add ht ht))
  exact .emul (by omega)
    (step_grade 2 (by omega) _ (step_grade 2 (by omega) _ (.add (.one 2) (.one 2)))) (.one 1)

 theorem closedSeed : SelectedOmegaSeedTargets.ClosedSeed := by
  intro ctrl
  have h := OmegaSeed.Proof.exactClosedSeed
  have he := exponent_calibration ctrl
  have ho := omega_calibration ctrl
  refine ⟨he.trans h.1,ho.trans h.2.1,omega_grade ctrl,?_,?_,?_⟩
  · rw [ho,h.2.1]
    exact Ordinal.opow_pos _ Ordinal.omega0_pos
  · exact SelectedValueClosureProof.closed_below ctrl OmegaSeed.omegaExpression
  · rw [ho]
    exact h.2.2.2.2
end LogicLineages.PermittedControl.SelectedOmegaSeed.Proof
