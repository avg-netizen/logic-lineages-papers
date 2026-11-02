module
public import LogicLineages.OrdinalComparison.GeneralOmegaHeadLimitDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GeneralOmegaHeadLimit.Targets
open ForwardTranslation

def GeneralPositiveLimit : Prop := ∀ a : Ordinal.{0}, 0 < a → a < epsilonZero →
  0 < omegaHead a ∧ Order.IsSuccLimit (omegaHead a) ∧ omegaHead a < epsilonZero

/-- The same evaluated actual head used by the source scalar compiler has a
normal notation and its existing literal numeric code, with no new oracle. -/
def ActualClosedHeadCalibration : Prop := ∀ a : ClosedPositive,
  (scalarHeadNote a).1.repr = fixedHead a ∧
  encodedClosedHead (closedPositiveCode a) = rawNoteEncode (scalarHeadNote a).1 ∧
  0 < fixedHead a ∧ Order.IsSuccLimit (fixedHead a) ∧ fixedHead a < epsilonZero
end LogicLineages.OrdinalComparison.Source.GeneralOmegaHeadLimit.Targets
