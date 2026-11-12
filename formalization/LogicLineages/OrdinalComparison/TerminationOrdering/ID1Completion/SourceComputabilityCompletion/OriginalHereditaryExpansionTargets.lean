module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansionTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryExpansion NumberedMultisetNumeric NumberedLeastCodeRepresentative
/-- Total numeric behavior, including malformed contexts/raw codes, uses the
existing total bounded deletion-row selector semantics unchanged. -/
def TotalCalibration : Prop := ∀ raw parameter : Nat,
  evaluate expansion (List.Vector.ofFn ![raw,parameter]) =
    numbersNumber (childValues raw parameter ++ deletionValues raw parameter)
/-- Exact one-node raw work expansion, ordered children first, then every
context deletion; multiplicities retained and original window c unchanged.
Not a recursive evaluator, typed child enumeration, or primitive-cost bound. -/
def SuccessorsCalibration : Prop := ∀ (n c : Nat)
    (s : OriginalHereditaryWorkBound.State (Fin n)),
  evaluate expansion (List.Vector.ofFn ![codeNumber s.code,
    Nat.pair c (Encodable.encode s.context)]) =
    numbersNumber ((OriginalHereditaryWorkBound.successors s).map (jobNumber c))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansionTargets
