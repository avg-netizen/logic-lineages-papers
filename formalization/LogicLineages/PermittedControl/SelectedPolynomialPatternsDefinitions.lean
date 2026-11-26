module
public import LogicLineages.PermittedControl.SelectedSystemReductionDefinitions
public import LogicLineages.PermittedControl.SelectedPolynomialLiftDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedPolynomialPatterns
open OrdinalComparison Source SourcePolynomialRealization SourceFiniteExponentProjection

noncomputable def polynomialEmbedding : PolynomialGroup →+ SignedPair.CantorGroup :=
  Finsupp.mapDomain.addMonoidHom (fun n : Nat => (n : Ordinal))

noncomputable def projectedPolynomial (a : Ordinal) : NonnegativePolynomial :=
  (finitePart (SignedPair.signedCNF a)).mapRange Int.toNat (by rfl)
end LogicLineages.PermittedControl.SelectedPolynomialPatterns
