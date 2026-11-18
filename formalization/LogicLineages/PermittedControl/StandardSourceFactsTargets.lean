module
public import LogicLineages.PermittedControl.StandardDomainCalibrationDefinitions
public import LogicLineages.PermittedControl.SelectedFunctionalDetectorDefinitions
public import LogicLineages.ControlSensitivityCurrent.FullAdditionTargets
@[expose] public section
namespace LogicLineages.PermittedControl.StandardSourceFactsTargets
open OrdinalComparison Source Source.AdmissibleSum

/-- Semantic ordinal bounds for every policy, not literal-node bounds. -/
def CanonicalFacts : Prop := ∀ (Γ : List Ty) (τ : Ty) (policy : Policy)
    (a : OriginalTerm Γ τ),
  ∃ v : OrdinalVector Γ τ.level,
    AdmissibleAssignment.assignment policy a=some v ∧
    (∀ j, SelectedSourceDomain.AmbientGrade Phi Γ j.val (v j)) ∧
    ∀ ρ : SelectedSourceDomain.AdmissibleSubstitution Phi Γ,
      ∃ n : Nat, 0 < n ∧
        SelectedSourceDomain.expressionValue Phi ρ (v 0)=(n : Ordinal) ∧
        SelectedSourceDomain.finiteValue (SelectedSourceDomain.expressionValue Phi ρ (v 0))=n ∧
        actualOrdinalNorm (SelectedSourceDomain.expressionValue Phi ρ (v 0))=n ∧
        (∀ j, 0 < SelectedSourceDomain.expressionValue Phi ρ (v j) ∧
          SelectedSourceDomain.expressionValue Phi ρ (v j)<epsilonZero ∧
          actualOrdinalNorm (SelectedSourceDomain.expressionValue Phi ρ (v j))≤n)

def UnaryFacts : Prop := ∀ (Γ : List Ty) (policy : Policy)
    (ρ : SelectedSourceDomain.AdmissibleSubstitution Phi Γ)
    (a : OriginalTerm Γ FunctionalDetector.unary),
  ∃ v : OrdinalVector Γ 1,
    AdmissibleAssignment.assignment policy a=some v ∧
    SelectedSourceDomain.expressionValue Phi ρ (v 0)=(SelectedHardness.value0 Phi policy ρ a : Ordinal) ∧
    SelectedSourceDomain.expressionValue Phi ρ (v 1)=SelectedHardness.value1 Phi policy ρ a ∧
    0 < SelectedHardness.value0 Phi policy ρ a ∧
    0 < SelectedHardness.value1 Phi policy ρ a ∧
    SelectedHardness.value1 Phi policy ρ a<epsilonZero ∧
    actualOrdinalNorm (SelectedHardness.value1 Phi policy ρ a)≤SelectedHardness.value0 Phi policy ρ a

def GroundFacts : Prop := ∀ (Γ : List Ty) (policy : Policy)
    (ρ : SelectedSourceDomain.AdmissibleSubstitution Phi Γ) (a : OriginalTerm Γ .ground),
  ∃ v : OrdinalVector Γ 0, AdmissibleAssignment.assignment policy a=some v ∧
    SelectedSourceDomain.expressionValue Phi ρ (v 0)=
      (SelectedFunctionalDetector.groundValue Phi policy ρ a : Ordinal) ∧
    0 < SelectedFunctionalDetector.groundValue Phi policy ρ a

/-- Only actual hierarchy facts, no source-success supplier premise. -/
def NumericalGrowth : Prop := StrictMono Phi ∧
  (∀ n : Nat, n < Phi n) ∧ ControlSensitivityCurrent.FullAddition.Targets.SourceGrowth Phi

def StandardSourceFacts : Prop := CanonicalFacts ∧ UnaryFacts ∧ GroundFacts ∧ NumericalGrowth
end LogicLineages.PermittedControl.StandardSourceFactsTargets
