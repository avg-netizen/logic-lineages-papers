module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RowDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion
open PolynomialGraphCompletion

/-- The actual emitted residual portion of counterExpansionRow, including its
integer correction. Only its leading ordinary leader term is removed here. -/
def counterResidualRow (a : Int) (i : Nat) (A : Word) (n c : Nat) : Row :=
  ((counterExpansionRow a i A n c).1,(counterExpansionRow a i A n c).2.tail)

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion
