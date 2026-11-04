module
public import LogicLineages.OrdinalComparison.SourceZeroPatternSubstitutionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceZeroPatternSubstitution.Targets

def ExactIndices : Prop := ∀ (n m : Nat) (r : Fin m → Fin n),Function.Injective r →
  (∀ j : Fin m,lookup r (r j)=some j) ∧
  (∀ i : Fin n,lookup r i=none ↔ i∉Set.range r) ∧
  (∀ (A : Type) [Zero A] (x : Fin m → A),
    (∀ j : Fin m,extend r x (r j)=x j) ∧
    (∀ i : Fin n,i∉Set.range r → extend r x i=0))

def OrdinalMeaningTransport : Prop := ∀ (n m : Nat) (r : Fin m → Fin n)
    (x : Fin m → Ordinal) (d : SignedPair.Expression n),
  Function.Injective r → SignedPair.meaning x (substitute r d)=SignedPair.meaning (extend r x) d

def PolynomialMeaningTransport : Prop := ∀ (n m : Nat) (r : Fin m → Fin n)
    (x : Fin m → SourceFiniteExponentProjection.PolynomialGroup) (d : SignedPair.Expression n),
  Function.Injective r →
    SourceFiniteExponentProjection.polynomialMeaning x (substitute r d)=
    SourceFiniteExponentProjection.polynomialMeaning (extend r x) d
end LogicLineages.OrdinalComparison.Source.SourceZeroPatternSubstitution.Targets
