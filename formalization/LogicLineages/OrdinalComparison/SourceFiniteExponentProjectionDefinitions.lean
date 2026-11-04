module
public import LogicLineages.OrdinalComparison.SourceSignedPairDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceFiniteExponentProjection
abbrev PolynomialGroup := Nat →₀ Int
noncomputable def finitePart (g : SignedPair.CantorGroup) : PolynomialGroup :=
  Finsupp.comapDomain (fun n : Nat => (n : Ordinal)) g Nat.cast_injective.injOn
noncomputable def polynomialShift (g : PolynomialGroup) : PolynomialGroup :=
  Finsupp.mapDomain Nat.succ g
noncomputable def polynomialMeaning {n : Nat} (x : Fin n → PolynomialGroup) :
    SignedPair.Expression n → PolynomialGroup
  | .unit => Finsupp.single 0 1
  | .var i => x i
  | .add a b => polynomialMeaning x a + polynomialMeaning x b
  | .neg a => -polynomialMeaning x a
  | .shift a => polynomialShift (polynomialMeaning x a)
end LogicLineages.OrdinalComparison.Source.SourceFiniteExponentProjection
