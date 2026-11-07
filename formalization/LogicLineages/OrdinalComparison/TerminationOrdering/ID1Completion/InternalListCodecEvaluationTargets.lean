module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector InternalListCodec

/-- Standard-model calibration is separate from the internal derivations. -/
def ExactListCodecEvaluation : Prop :=
  (∀ h t : Nat, evaluate consCode (h ::ᵥ t ::ᵥ List.Vector.nil) = 1 + Nat.pair h t) ∧
  (∀ n : Nat,
    evaluate headCode (n ::ᵥ List.Vector.nil) = (Nat.unpair (n-1)).1 ∧
    evaluate tailCode (n ::ᵥ List.Vector.nil) = (Nat.unpair (n-1)).2 ∧
    evaluate nilTest (n ::ᵥ List.Vector.nil) = if n=0 then 1 else 0)

/-- Calibration names the unchanged original list encoder itself. It does not
assert that arbitrary codes were successfully decoded as canonical lists. -/
def ExactSourceListEncoding : Prop :=
  (NumberedMultisetNumeric.numbersNumber [] = 0 ∧
    evaluate nilTest (NumberedMultisetNumeric.numbersNumber [] ::ᵥ List.Vector.nil) = 1) ∧
  ∀ (h : Nat) (t : List Nat),
  evaluate consCode (h ::ᵥ NumberedMultisetNumeric.numbersNumber t ::ᵥ List.Vector.nil) =
    NumberedMultisetNumeric.numbersNumber (h::t) ∧
  evaluate headCode (NumberedMultisetNumeric.numbersNumber (h::t) ::ᵥ List.Vector.nil) = h ∧
  evaluate tailCode (NumberedMultisetNumeric.numbersNumber (h::t) ::ᵥ List.Vector.nil) =
    NumberedMultisetNumeric.numbersNumber t ∧
  evaluate nilTest (NumberedMultisetNumeric.numbersNumber (h::t) ::ᵥ List.Vector.nil) = 0

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationTargets
