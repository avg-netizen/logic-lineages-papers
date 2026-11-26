module
public import LogicLineages.PermittedControl.SelectedPolynomialLiftDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedPolynomialLiftTargets
open OrdinalComparison Source SelectedSourceDomain SelectedPolynomialLift
open SourcePolynomialRealization SourcePolynomialFamilyLift

/-- Genuine ctrl-valued grade, not a fixed-control semantic transfer. -/
def GradedRealization : Prop := ∀ (ctrl : Nat → Nat) (p : NonnegativePolynomial),
  p≠0 → ∃ t : ClosedExpression, ClosedGrade ctrl 1 t ∧
    SignedPair.signedCNF (closedValue ctrl t)=embeddedCoefficients p ∧
    0<closedValue ctrl t ∧ closedValue ctrl t<Ordinal.omega0^Ordinal.omega0

/-- Actual scalar padding derives whole-vector boundedness. -/
def ExactPaddedVector : Prop := ∀ (ctrl : Nat → Nat) (t : ClosedExpression),
  ClosedGrade ctrl 1 t →
  (∀ j : Fin 2, ClosedGrade ctrl j.val (vector ctrl t j)) ∧
  (∀ j : Fin 2, actualOrdinalNorm (closedValue ctrl (vector ctrl t j))≤
    actualOrdinalNorm (closedValue ctrl (vector ctrl t 0))) ∧
  closedValue ctrl (vector ctrl t 0)=((actualOrdinalNorm (closedValue ctrl t)+1 : Nat) : Ordinal) ∧
  closedValue ctrl (vector ctrl t 1)=closedValue ctrl t

/-- Simultaneous actual context extension, including empty families and arbitrary old types. -/
def SimultaneousExtension : Prop := ∀ (ctrl : Nat → Nat) (Γ : List Ty)
    (ρ : AdmissibleSubstitution ctrl Γ) (n : Nat) (p : Fin n → NonnegativePolynomial),
  (∀ i,p i≠0) → ∃ σ : AdmissibleSubstitution ctrl (List.replicate n FunctionalDetector.unary ++ Γ),
  (∀ i : Fin n,
    SignedPair.signedCNF (closedValue ctrl (σ.vector (prefixVariable Γ i) 1))=embeddedCoefficients (p i) ∧
    0<closedValue ctrl (σ.vector (prefixVariable Γ i) 1) ∧
    closedValue ctrl (σ.vector (prefixVariable Γ i) 1)<Ordinal.omega0^Ordinal.omega0 ∧
    closedValue ctrl (σ.vector (prefixVariable Γ i) 0)=
      ((actualOrdinalNorm (closedValue ctrl (σ.vector (prefixVariable Γ i) 1))+1 : Nat) : Ordinal)) ∧
  (∀ (τ : Ty) (x : Variable Γ τ) (j : Fin (τ.level+1)),
    σ.vector (oldVariable Γ τ n x) j=ρ.vector x j)

/-- Exact original n-variable selected input interpretation, no added free seed. -/
def SignedInputCalibration : Prop := ∀ (ctrl : Nat → Nat) (n : Nat)
    (p : Fin n → NonnegativePolynomial), (∀ i,p i≠0) →
  ∃ ρ : AdmissibleSubstitution ctrl (SignedPair.Context n), ∀ i : Fin n,
    SignedPair.signedCNF (SelectedPairCompiler.inputs ctrl ρ i)=embeddedCoefficients (p i) ∧
    0<SelectedPairCompiler.inputs ctrl ρ i ∧
    SelectedPairCompiler.inputs ctrl ρ i<Ordinal.omega0^Ordinal.omega0 ∧
    closedValue ctrl (ρ.vector (SignedPair.inputVariable i) 0)=
      ((actualOrdinalNorm (SelectedPairCompiler.inputs ctrl ρ i)+1 : Nat) : Ordinal)

def SelectedPolynomialLift : Prop :=
  GradedRealization ∧ ExactPaddedVector ∧ SimultaneousExtension ∧ SignedInputCalibration
end LogicLineages.PermittedControl.SelectedPolynomialLiftTargets
