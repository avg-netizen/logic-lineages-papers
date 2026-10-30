module
public import LogicLineages.OrdinalComparison.ResidueTupleDefinitions
public import LogicLineages.OrdinalComparison.CartierRationalDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- The genuine source differential omega_e, represented by its coefficient
in the actual rational function field over the algebraic closure of F2. -/
noncomputable def actualLinkedDifferential (u : Nat) : RatFunc ActualResidueField :=
  algebraMap (Polynomial ActualResidueField) (RatFunc ActualResidueField)
      (Polynomial.X ^ (actualLinkedOffset u - 1)) /
    algebraMap (Polynomial ActualResidueField) (RatFunc ActualResidueField)
      ((actualBinarySourceDenominator (actualLinkedCutoff u)).map
        (algebraMap (ZMod 2) ActualResidueField))

end LogicLineages.OrdinalComparison
