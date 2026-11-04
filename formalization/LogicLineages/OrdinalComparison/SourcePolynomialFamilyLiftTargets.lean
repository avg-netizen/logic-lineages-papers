module
public import LogicLineages.OrdinalComparison.SourcePolynomialFamilyLiftDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePolynomialFamilyLift.Targets
open OriginalDomain SourcePolynomialRealization

def SimultaneousExtension : Prop := ∀ (Γ : List Ty) (ρ : AdmissibleSubstitution Γ)
    (n : Nat) (p : Fin n → NonnegativePolynomial), (∀ i,p i≠0) →
  ∃ σ : AdmissibleSubstitution (List.replicate n FunctionalDetector.unary ++ Γ),
    (∀ i : Fin n,
      SignedPair.signedCNF (closedValue (σ.vector (prefixVariable Γ i) 1))=embeddedCoefficients (p i) ∧
      0<closedValue (σ.vector (prefixVariable Γ i) 1) ∧
      closedValue (σ.vector (prefixVariable Γ i) 1)<Ordinal.omega0^Ordinal.omega0 ∧
      closedValue (σ.vector (prefixVariable Γ i) 0)=
        ((actualOrdinalNorm (closedValue (σ.vector (prefixVariable Γ i) 1))+1:Nat):Ordinal)) ∧
    (∀ (τ : Ty) (x : Variable Γ τ) (j : Fin (τ.level+1)),
      σ.vector (oldVariable Γ τ n x) j=ρ.vector x j)

def SignedInputCalibration : Prop := ∀ (n : Nat) (p : Fin n → NonnegativePolynomial),
  (∀ i,p i≠0) → ∃ ρ : AdmissibleSubstitution (SignedPair.Context n),
    ∀ i : Fin n,
      SignedPair.signedCNF (SignedPair.inputs ρ i)=embeddedCoefficients (p i) ∧
      0<SignedPair.inputs ρ i ∧ SignedPair.inputs ρ i<Ordinal.omega0^Ordinal.omega0 ∧
      closedValue (ρ.vector (SignedPair.inputVariable i) 0)=
        ((actualOrdinalNorm (SignedPair.inputs ρ i)+1:Nat):Ordinal)
end LogicLineages.OrdinalComparison.Source.SourcePolynomialFamilyLift.Targets
