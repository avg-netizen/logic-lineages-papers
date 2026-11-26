module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityEqualityBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceNumericProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceDecreaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceRankProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityEqualityNumericProof
open OriginalHereditaryValidity OriginalTransparentLambdaValidity
open OriginalHereditaryValidityRecurrenceNumericProof
open OriginalHereditaryValidityRecurrenceSourceDecreaseProof
open OriginalHereditaryValidityRecurrenceSourceRankProof

/-- Payload induction for the literal bounded machine, with independently
changing parameters. The hypotheses are native leaf equations, not graph laws. -/
theorem transparentNumericEquality (S T M : Nat → Nat → Nat)
    (sbool : ∀ v p, S v p = 0 ∨ S v p = 1)
    (tbool : ∀ v p, T v p = 0 ∨ T v p = 1)
    (st : ∀ v p, S v p = 1 → T v p = 1)
    (app : ∀ v p, tagValue v = 2 →
      (T v p = if T (functionChildValue v) p = 1 ∧ T (argumentChildValue v) p = 1 then 1 else 0) ∧
      (S v p = if M (resultTypeValue v) p = 1 ∧ S (functionChildValue v) p = 1 ∧
        S (argumentChildValue v) p = 1 then 1 else 0))
    (lam : ∀ v p, tagValue v = 1 →
      (T v p = if lambdaShapeValue v = 1 ∧ T (lambdaBodyValue v) (childParameterValue v p) = 1 then 1 else 0) ∧
      (S v p = if lambdaShapeValue v = 1 ∧ M (resultTypeValue v) p = 1 ∧
        M (domainValue v) p = 1 ∧ S (lambdaBodyValue v) (childParameterValue v p) = 1 then 1 else 0)) :
    ∀ v p,
      validatorValue (sourceRootValue S M) (targetRootValue T) M v p = S v p ∧
      validatorValue (targetRootValue T) (fun _ _ => 1) (fun _ _ => 1) v p = T v p := by
  suffices hall : ∀ v p, True →
      validatorValue (sourceRootValue S M) (targetRootValue T) M v p = S v p ∧
      validatorValue (targetRootValue T) (fun _ _ => 1) (fun _ _ => 1) v p = T v p by
    intro v p
    exact hall v p trivial
  apply binaryRankInduction payloadValue (fun _ _ => True)
    (fun v p =>
      validatorValue (sourceRootValue S M) (targetRootValue T) M v p = S v p ∧
      validatorValue (targetRootValue T) (fun _ _ => 1) (fun _ _ => 1) v p = T v p)
  intro v p ih _
  by_cases ha : tagValue v = 2
  · exact OriginalTransparentLambdaValidityEqualityBranchProof.applicationOutput S T M v p
      (sbool v p) (tbool v p) ha
      (ih (functionChildValue v) p (functionPayloadLess v ha) trivial)
      (ih (argumentChildValue v) p (argumentPayloadLess v ha) trivial) (app v p ha)
  · by_cases hl : tagValue v = 1
    · exact OriginalTransparentLambdaValidityEqualityBranchProof.lambdaOutput S T M v p
        (sbool v p) (tbool v p) hl
        (ih (lambdaBodyValue v) (childParameterValue v p) (lambdaPayloadLess v hl) trivial)
        (lam v p hl)
    · exact OriginalTransparentLambdaValidityEqualityBranchProof.opaqueOutput S T M v p
        (sbool v p) (tbool v p) ha hl (st v p)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityEqualityNumericProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityEqualityNumericProof
