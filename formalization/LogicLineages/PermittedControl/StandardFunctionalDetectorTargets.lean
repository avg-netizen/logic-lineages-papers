module
public import LogicLineages.PermittedControl.StandardCombinatorCoordinatesTargets
@[expose] public section
namespace LogicLineages.PermittedControl.StandardFunctionalDetector
open OrdinalComparison Source Source.AdmissibleSum SelectedSourceDomain SelectedFunctionalDetector
open Source.FunctionalDetector (unary alignedLeft alignedRight shiftTwo left right)

def ExtensionCalibration : Prop :=
  (∀ n : Nat, closedValue Phi (UnitObservation.positive n)=((n+1 : Nat) : Ordinal)) ∧
  ∀ (Γ : List Ty) (ρ : AdmissibleSubstitution Phi Γ) (z w : Nat),
    expressionValue Phi (extend Phi ρ z w) (.var ⟨.ground,.here,0⟩)=((z+1 : Nat) : Ordinal) ∧
    expressionValue Phi (extend Phi ρ z w) (.var ⟨.ground,.there .here,0⟩)=((w+1 : Nat) : Ordinal) ∧
    (∀ (τ : Ty) (x : Variable Γ τ) (j : Fin (τ.level+1)),
      (extend Phi ρ z w).vector (.there (.there x)) j=ρ.vector x j) ∧
    (∀ e : OrdinalExpression Γ,
      expressionValue Phi (extend Phi ρ z w) (ordinalExpressionRename (shiftTwo Γ) e)=
        expressionValue Phi ρ e)

def Alignment : Prop := ∀ (Γ : List Ty) (p : Policy)
    (a b : OriginalTerm Γ unary) (ρ : AdmissibleSubstitution Phi Γ),
  HeadEqual Phi p ρ a b ↔ ∃ z w : Nat,
    VectorEqual Phi p (extend Phi ρ z w) (alignedLeft a) (alignedRight b)

def Detector : Prop := ∀ (Γ : List Ty) (p : Policy)
    (a b : OriginalTerm Γ unary) (ρ : AdmissibleSubstitution Phi Γ),
  Detects Phi p ρ a b ∧
    0 < groundValue Phi p ρ (left a b) ∧ 0 < groundValue Phi p ρ (right a b)

def StandardFunctionalDetector : Prop := ExtensionCalibration ∧ Alignment ∧ Detector
end LogicLineages.PermittedControl.StandardFunctionalDetector
