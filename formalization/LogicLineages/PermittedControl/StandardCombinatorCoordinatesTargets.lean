module
public import LogicLineages.PermittedControl.StandardApplicationEraserTargets
@[expose] public section
namespace LogicLineages.PermittedControl.StandardCombinatorCoordinates
open OrdinalComparison Source Source.AdmissibleSum Source.AdmissibleAssignment
open SelectedSourceDomain SelectedHardness

def UnaryOutput {Γ : List Ty} (p : Policy) (ρ : AdmissibleSubstitution Phi Γ)
    (a : OriginalTerm Γ unary) : Prop :=
  ∃ v : OrdinalVector Γ 1, assignment p a=some v ∧
    expressionValue Phi ρ (v 0)=(value0 Phi p ρ a : Ordinal) ∧
    expressionValue Phi ρ (v 1)=value1 Phi p ρ a ∧
    0 < value0 Phi p ρ a ∧ 0 < value1 Phi p ρ a ∧
    value1 Phi p ρ a<epsilonZero ∧ actualOrdinalNorm (value1 Phi p ρ a)≤value0 Phi p ρ a

def SuccessfulOutputs : Prop := ∀ (Γ : List Ty) (p : Policy)
    (ρ : AdmissibleSubstitution Phi Γ) (a b : OriginalTerm Γ unary) (q : OriginalTerm Γ .ground),
  UnaryOutput p ρ (identity (Γ:=Γ)) ∧ UnaryOutput p ρ (project a b) ∧
    UnaryOutput p ρ (combine a b) ∧ UnaryOutput p ρ (liftOmega a) ∧
    UnaryOutput p ρ (FunctionalDetector.pad a q)

def CombinatorValues : Prop := ∀ (Γ : List Ty) (p : Policy) (ρ : AdmissibleSubstitution Phi Γ)
    (a b : OriginalTerm Γ unary),
  value1 Phi p ρ (identity (Γ := Γ)) = 1 ∧
  value1 Phi p ρ (project a b) = projectHead (value1 Phi p ρ a) (value1 Phi p ρ b) ∧
  value1 Phi p ρ (combine a b) = combineHead (value1 Phi p ρ a) (value1 Phi p ρ b) ∧
  value0 Phi p ρ (combine a b) = ParametricActualCollapse.collapseWith Phi
    (ordinalNaturalProduct Ordinal.omega0 (combineHead (value1 Phi p ρ a) (value1 Phi p ρ b)) +
      ((9*value0 Phi p ρ a+5*value0 Phi p ρ b+13 : Nat) : Ordinal)) ∧
  value1 Phi p ρ (liftOmega a) = liftHead (value1 Phi p ρ a)

def SignedCombinatorValues : Prop := ∀ (Γ : List Ty) (p : Policy) (ρ : AdmissibleSubstitution Phi Γ)
    (a b : OriginalTerm Γ unary),
  Source.SignedPair.signedCNF (value1 Phi p ρ (project a b)) =
    (8 : Int) • Source.SignedPair.signedCNF (value1 Phi p ρ a) +
    (4 : Int) • Source.SignedPair.signedCNF (value1 Phi p ρ b) +
    (8 : Int) • Source.SignedPair.signedCNF 1 ∧
  Source.SignedPair.signedCNF (value1 Phi p ρ (combine a b)) =
    (8 : Int) • Source.SignedPair.signedCNF (value1 Phi p ρ a) +
    (8 : Int) • Source.SignedPair.signedCNF (value1 Phi p ρ b) +
    (16 : Int) • Source.SignedPair.signedCNF 1 ∧
  Source.SignedPair.signedCNF (value1 Phi p ρ (liftOmega a)) =
    (2 : Int) • Source.SignedPair.omegaShift (Source.SignedPair.signedCNF (value1 Phi p ρ a)) +
    (3 : Int) • Source.SignedPair.signedCNF Ordinal.omega0

def PadValues : Prop := ∀ (Γ : List Ty) (p : Policy)
    (ρ : AdmissibleSubstitution Phi Γ) (a : OriginalTerm Γ unary) (q : OriginalTerm Γ .ground),
  value1 Phi p ρ (FunctionalDetector.pad a q)=paddedHead (value1 Phi p ρ a) ∧
    value0 Phi p ρ (FunctionalDetector.pad a q)=ParametricActualCollapse.collapseWith Phi
      (ordinalNaturalProduct Ordinal.omega0 (paddedHead (value1 Phi p ρ a))+
        ((5*value0 Phi p ρ a+4+SelectedFunctionalDetector.groundValue Phi p ρ q : Nat) : Ordinal))

def StandardCombinatorCoordinates : Prop := SuccessfulOutputs ∧ CombinatorValues ∧
  SignedCombinatorValues ∧ PadValues
end LogicLineages.PermittedControl.StandardCombinatorCoordinates
