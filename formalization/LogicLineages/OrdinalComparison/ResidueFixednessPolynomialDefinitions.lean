module
public import LogicLineages.OrdinalComparison.LinkedResidueLaurentDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Literal polynomial P_s in paper10 thm:actual-period. All natural
subtractions are calibrated by u>=5 and s>0 in the supplied theorems. -/
noncomputable def actualResidueFixednessPolynomial (u s : Nat) : Polynomial (ZMod 2) :=
  actualBinarySourceDenominator (actualLinkedTail u) ^ (2 ^ s) +
    Polynomial.X ^ ((actualLinkedDegree u - actualLinkedOffset u) * (2 ^ s - 1)) *
      actualBinarySourceDenominator (actualLinkedTail u)

end LogicLineages.OrdinalComparison
