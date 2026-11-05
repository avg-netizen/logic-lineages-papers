module
public import LogicLineages.OrdinalComparison.WWEncodedClosedPositiveDefinitions
public import LogicLineages.OrdinalComparison.EncodedDescentDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBaseDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticCoefficient.Code

/-- Evaluate the actual closed coefficient syntax to its normal ordinal code,
then use the exact existing finite-ordinal test and value extractor. This is a
separate consumer, not a change to the accepted structural scalar compiler. -/
def recognize (code : Nat) : Option Nat :=
  let value := Source.ForwardTranslation.encodedClosedPositive code
  if encodedFiniteTest value then some (encodedFiniteValue value) else none

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticCoefficient.Code
