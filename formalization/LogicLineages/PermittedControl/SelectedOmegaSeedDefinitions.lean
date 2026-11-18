module
public import LogicLineages.PermittedControl.SelectedPairCompilerDefinitions
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.OmegaSeedDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedOmegaSeed
open OrdinalComparison Source SelectedSourceDomain
open Source.AdmissibleSum
open Source.FunctionalHardnessCompletion

/-- Actual selected value of the printed closed exponent expression. -/
noncomputable def exponent (ctrl : Nat → Nat) : Ordinal :=
  closedValue ctrl OmegaSeed.exponentExpression
noncomputable def omega (ctrl : Nat → Nat) : Ordinal :=
  closedValue ctrl OmegaSeed.omegaExpression

/-- Actual policy assignment of the printed higher-type source, not an old control proxy. -/
noncomputable def secondValue {Γ} (ctrl : Nat → Nat) (policy : Policy)
    (ρ : AdmissibleSubstitution ctrl Γ) (a : OriginalTerm Γ OmegaSeed.higherUnary) : Ordinal :=
  ((AdmissibleAssignment.assignment policy a).map
    (fun v => expressionValue ctrl ρ (v 2))).getD 0
end LogicLineages.PermittedControl.SelectedOmegaSeed
