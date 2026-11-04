module
public import LogicLineages.OrdinalComparison.SourceUnaryNormPaddingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceUnaryNormPadding.Targets
open OriginalDomain

def ExactVector : Prop := ∀ t : ClosedExpression, ClosedGrade 1 t →
  (∀ j : Fin 2,ClosedGrade j.val (vector t j)) ∧
  (∀ j : Fin 2,actualOrdinalNorm (closedValue (vector t j)) ≤
    actualOrdinalNorm (closedValue (vector t 0))) ∧
  closedValue (vector t 0)=((actualOrdinalNorm (closedValue t)+1:Nat):Ordinal) ∧
  closedValue (vector t 1)=closedValue t

def AdmissibleExtension : Prop := ∀ (Γ : List Ty) (ρ : AdmissibleSubstitution Γ)
    (t : ClosedExpression), ClosedGrade 1 t →
  ∃ σ : AdmissibleSubstitution (FunctionalDetector.unary::Γ),
    (∀ j : Fin 2,σ.vector .here j=vector t j) ∧
    (∀ (τ : Ty) (x : Variable Γ τ) (j : Fin (τ.level+1)),σ.vector (.there x) j=ρ.vector x j)

def PolynomialExtension : Prop := ∀ (Γ : List Ty) (ρ : AdmissibleSubstitution Γ)
    (p : SourcePolynomialRealization.NonnegativePolynomial),p≠0 →
  ∃ σ : AdmissibleSubstitution (FunctionalDetector.unary::Γ),
    SignedPair.signedCNF (closedValue (σ.vector .here 1))=SourcePolynomialRealization.embeddedCoefficients p ∧
    0<closedValue (σ.vector .here 1) ∧
    closedValue (σ.vector .here 1)<Ordinal.omega0^Ordinal.omega0 ∧
    closedValue (σ.vector .here 0)=((actualOrdinalNorm (closedValue (σ.vector .here 1))+1:Nat):Ordinal) ∧
    (∀ (τ : Ty) (x : Variable Γ τ) (j : Fin (τ.level+1)),σ.vector (.there x) j=ρ.vector x j)
end LogicLineages.OrdinalComparison.Source.SourceUnaryNormPadding.Targets
