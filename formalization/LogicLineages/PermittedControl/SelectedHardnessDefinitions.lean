module
public import LogicLineages.PermittedControl.SelectedCanonicalDomainTargets
public import LogicLineages.OrdinalComparison.SourceSignedPairDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedHardness
open OrdinalComparison Source Source.AdmissibleSum Source.AdmissibleAssignment
open SelectedSourceDomain
abbrev unary := Source.FunctionalDetector.unary

/-- Actual selected interpretation of the actual policy assignment, never a fixed-G proxy. -/
noncomputable def value0 {Γ} (ctrl : Nat → Nat) (p : Policy)
    (ρ : AdmissibleSubstitution ctrl Γ) (a : OriginalTerm Γ unary) : Nat :=
  ((assignment p a).map (fun v => finiteValue (expressionValue ctrl ρ (v 0)))).getD 0
noncomputable def value1 {Γ} (ctrl : Nat → Nat) (p : Policy)
    (ρ : AdmissibleSubstitution ctrl Γ) (a : OriginalTerm Γ unary) : Ordinal :=
  ((assignment p a).map (fun v => expressionValue ctrl ρ (v 1))).getD 0

/-- Literal manuscript P, S, H, and C; only their old syntax is reused. -/
abbrev project := @Source.SignedPair.project
abbrev combine := @Source.FunctionalDetector.combine
abbrev liftOmega := @Source.SignedPair.liftOmega
abbrev identity := @Source.SignedPair.identity

noncomputable def paddedHead (a : Ordinal) : Ordinal :=
  ordinalNaturalSum (ordinalNaturalSum 1 (ordinalNaturalSum a 1)) a
noncomputable def projectHead (a b : Ordinal) : Ordinal :=
  ordinalNaturalProduct 4 (ordinalNaturalSum (paddedHead a) b)
noncomputable def combineHead (a b : Ordinal) : Ordinal :=
  ordinalNaturalProduct 4 (ordinalNaturalSum (paddedHead a) (paddedHead b))
noncomputable def liftHead (a : Ordinal) : Ordinal :=
  ordinalNaturalSum (ordinalNaturalProduct 2 (ordinalNaturalProduct Ordinal.omega0 a))
    (ordinalNaturalProduct 3 Ordinal.omega0)

end LogicLineages.PermittedControl.SelectedHardness
