module
public import LogicLineages.PermittedControl.SelectedFunctionalDetectorDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedFunctionalDetectorTargets
open OrdinalComparison Source Source.AdmissibleSum SelectedSourceDomain SelectedFunctionalDetector
open Source.FunctionalDetector (unary alignedLeft alignedRight)

/-- The actual fresh positive inputs encode precisely z+1,w+1, not default zeros. -/
def PositiveExtensionCalibration : Prop := ∀ (ctrl : Nat → Nat) (n : Nat),
  closedValue ctrl (UnitObservation.positive n)=((n+1 : Nat) : Ordinal)

/-- Complete current Paper17 lem:functional-detector with no restrictions on
actual unary sources or their admissible selected valuations, for every policy. -/
def AlignmentAndDetector : Prop := ∀ (ctrl : Nat → Nat) (K : Nat),
  SelectedWithThreshold ctrl K → ∀ (Γ : List Ty) (p : Policy)
    (a b : OriginalTerm Γ unary) (ρ : AdmissibleSubstitution ctrl Γ),
  (HeadEqual ctrl p ρ a b ↔ ∃ z w : Nat,
    VectorEqual ctrl p (extend ctrl ρ z w) (alignedLeft a) (alignedRight b)) ∧
  Detects ctrl p ρ a b

def FullSelectedFunctionalDetector : Prop :=
  PositiveExtensionCalibration ∧ AlignmentAndDetector
end LogicLineages.PermittedControl.SelectedFunctionalDetectorTargets
