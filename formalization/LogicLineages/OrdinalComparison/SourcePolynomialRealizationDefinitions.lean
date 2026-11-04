module
public import LogicLineages.OrdinalComparison.SourceFiniteExponentProjectionDefinitions
public import LogicLineages.OrdinalComparison.PolynomialOrdinalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePolynomialRealization
abbrev NonnegativePolynomial := Nat →₀ Nat
noncomputable def signedCoefficients (p : NonnegativePolynomial) : Nat →₀ Int :=
  p.mapRange (fun n : Nat => (n : Int)) (by simp)
noncomputable def embeddedCoefficients (p : NonnegativePolynomial) : SignedPair.CantorGroup :=
  Finsupp.mapDomain (fun n : Nat => (n : Ordinal)) (signedCoefficients p)
end LogicLineages.OrdinalComparison.Source.SourcePolynomialRealization
