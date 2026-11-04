module
public import LogicLineages.OrdinalComparison.SourcePolynomialRealizationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePolynomialRealization.Targets

def ExactEmbedding : Prop := ∀ p : NonnegativePolynomial,
  (∀ n : Nat,embeddedCoefficients p (n:Ordinal)=(p n:Int)) ∧
  (∀ e : Ordinal,Ordinal.omega0≤e → embeddedCoefficients p e=0) ∧
  SourceFiniteExponentProjection.finitePart (embeddedCoefficients p)=signedCoefficients p

def ActualRealization : Prop := ∀ p : NonnegativePolynomial,
  ∃ a : Ordinal.{0}, a < Ordinal.omega0 ^ Ordinal.omega0 ∧
    SignedPair.signedCNF a=embeddedCoefficients p ∧
    SourceFiniteExponentProjection.finitePart (SignedPair.signedCNF a)=signedCoefficients p ∧
    (a=0 ↔ p=0) ∧ (0<a ↔ p≠0)
end LogicLineages.OrdinalComparison.Source.SourcePolynomialRealization.Targets
