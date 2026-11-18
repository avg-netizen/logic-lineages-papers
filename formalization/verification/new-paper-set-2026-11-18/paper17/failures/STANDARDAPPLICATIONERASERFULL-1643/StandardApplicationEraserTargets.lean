module
public import LogicLineages.PermittedControl.StandardDetectorNumericTargets
@[expose] public section
namespace LogicLineages.PermittedControl.StandardApplicationEraser
open OrdinalComparison Source Source.AdmissibleSum

/-- Genuine successful finite positive output, not a default-zero wrapper alone. -/
def GroundOutput {Γ : List Ty} (policy : Policy)
    (ρ : SelectedSourceDomain.AdmissibleSubstitution Phi Γ)
    (a : OriginalTerm Γ .ground) : Prop :=
  ∃ v : OrdinalVector Γ 0, AdmissibleAssignment.assignment policy a=some v ∧
    SelectedSourceDomain.expressionValue Phi ρ (v 0)=
      (SelectedFunctionalDetector.groundValue Phi policy ρ a : Ordinal) ∧
    0 < SelectedFunctionalDetector.groundValue Phi policy ρ a

def ZeroCalibration : Prop := ∀ (Γ : List Ty) (policy : Policy)
    (ρ : SelectedSourceDomain.AdmissibleSubstitution Phi Γ),
  GroundOutput policy ρ OriginalTerm.zeroC ∧
    SelectedFunctionalDetector.groundValue Phi policy ρ OriginalTerm.zeroC=1

def ApplicationCalibration : Prop := ∀ (Γ : List Ty) (policy : Policy)
    (ρ : SelectedSourceDomain.AdmissibleSubstitution Phi Γ)
    (a : OriginalTerm Γ FunctionalDetector.unary) (q : OriginalTerm Γ .ground),
  GroundOutput policy ρ (.app a q) ∧
    SelectedFunctionalDetector.groundValue Phi policy ρ (.app a q)=
      StandardDetectorNumeric.appValue (SelectedHardness.value1 Phi policy ρ a)
        (SelectedHardness.value0 Phi policy ρ a) (SelectedFunctionalDetector.groundValue Phi policy ρ q)

def EraserCalibration : Prop := ∀ (Γ : List Ty) (policy : Policy)
    (ρ : SelectedSourceDomain.AdmissibleSubstitution Phi Γ)
    (a b : OriginalTerm Γ .ground),
  GroundOutput policy ρ (SourceCollisionCompletion.eraser a b) ∧
    SelectedFunctionalDetector.groundValue Phi policy ρ (SourceCollisionCompletion.eraser a b)=
      ParametricActualCollapse.collapseWith Phi (Ordinal.omega0+
        ((3*SelectedFunctionalDetector.groundValue Phi policy ρ a+
          SelectedFunctionalDetector.groundValue Phi policy ρ b+2 : Nat) : Ordinal))

def StandardApplicationEraser : Prop := ZeroCalibration ∧ ApplicationCalibration ∧ EraserCalibration
end LogicLineages.PermittedControl.StandardApplicationEraser
