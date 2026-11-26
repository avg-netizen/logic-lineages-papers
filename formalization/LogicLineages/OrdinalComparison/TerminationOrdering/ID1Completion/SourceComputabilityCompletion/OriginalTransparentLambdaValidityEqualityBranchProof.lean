module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceNumericProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceDecreaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceRankProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityEqualityBranchProof
open OriginalHereditaryValidity OriginalTransparentLambdaValidity
open OriginalHereditaryValidityRecurrenceNumericProof
open OriginalHereditaryValidityRecurrenceSourceDecreaseProof
open OriginalHereditaryValidityRecurrenceSourceRankProof

theorem booleanEquality {a b : Nat} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (hab : a = 1 ↔ b = 1) : a = b := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega

theorem applicationOutput (S T M : Nat → Nat → Nat) (v p : Nat)
    (sbool : S v p = 0 ∨ S v p = 1) (tbool : T v p = 0 ∨ T v p = 1)
    (ha : tagValue v = 2)
    (hf : (validatorValue (sourceRootValue S M) (targetRootValue T) M (functionChildValue v) p = S (functionChildValue v) p ∧
      validatorValue (targetRootValue T) (fun _ _ => 1) (fun _ _ => 1) (functionChildValue v) p = T (functionChildValue v) p))
    (hg : (validatorValue (sourceRootValue S M) (targetRootValue T) M (argumentChildValue v) p = S (argumentChildValue v) p ∧
      validatorValue (targetRootValue T) (fun _ _ => 1) (fun _ _ => 1) (argumentChildValue v) p = T (argumentChildValue v) p))
    (he : (T v p = if T (functionChildValue v) p = 1 ∧ T (argumentChildValue v) p = 1 then 1 else 0) ∧
      (S v p = if M (resultTypeValue v) p = 1 ∧ S (functionChildValue v) p = 1 ∧ S (argumentChildValue v) p = 1 then 1 else 0)) :
    validatorValue (sourceRootValue S M) (targetRootValue T) M v p = S v p ∧
    validatorValue (targetRootValue T) (fun _ _ => 1) (fun _ _ => 1) v p = T v p := by
  have hs := actualOriginalHereditaryValidatorRecurrence (sourceRootValue S M) (targetRootValue T) M v p
  have ht := actualOriginalHereditaryValidatorRecurrence (targetRootValue T) (fun _ _ => 1) (fun _ _ => 1) v p
  constructor
  · apply booleanEquality hs.1 sbool
    rw [hs.2]
    simp [nodeCheckValue, sourceRootValue, targetRootValue, ha, hf.1, hg.1, he.2]
  · apply booleanEquality ht.1 tbool
    rw [ht.2]
    simp [nodeCheckValue, targetRootValue, ha, hf.2, hg.2, he.1]

theorem lambdaOutput (S T M : Nat → Nat → Nat) (v p : Nat)
    (sbool : S v p = 0 ∨ S v p = 1) (tbool : T v p = 0 ∨ T v p = 1)
    (hl : tagValue v = 1)
    (hb : (validatorValue (sourceRootValue S M) (targetRootValue T) M (lambdaBodyValue v) (childParameterValue v p) = S (lambdaBodyValue v) (childParameterValue v p) ∧
      validatorValue (targetRootValue T) (fun _ _ => 1) (fun _ _ => 1) (lambdaBodyValue v) (childParameterValue v p) = T (lambdaBodyValue v) (childParameterValue v p)))
    (he : (T v p = if lambdaShapeValue v = 1 ∧ T (lambdaBodyValue v) (childParameterValue v p) = 1 then 1 else 0) ∧
      (S v p = if lambdaShapeValue v = 1 ∧ M (resultTypeValue v) p = 1 ∧ M (domainValue v) p = 1 ∧
        S (lambdaBodyValue v) (childParameterValue v p) = 1 then 1 else 0)) :
    validatorValue (sourceRootValue S M) (targetRootValue T) M v p = S v p ∧
    validatorValue (targetRootValue T) (fun _ _ => 1) (fun _ _ => 1) v p = T v p := by
  have hs := actualOriginalHereditaryValidatorRecurrence (sourceRootValue S M) (targetRootValue T) M v p
  have ht := actualOriginalHereditaryValidatorRecurrence (targetRootValue T) (fun _ _ => 1) (fun _ _ => 1) v p
  constructor
  · apply booleanEquality hs.1 sbool
    rw [hs.2]
    by_cases hshape : lambdaShapeValue v = 1
    · by_cases htype : M (resultTypeValue v) p = 1
      · by_cases hdomain : M (domainValue v) p = 1 <;>
          simp [nodeCheckValue, sourceRootValue, targetRootValue, hl, hb.1, he.2,
            hshape, htype, hdomain]
      · simp [nodeCheckValue, sourceRootValue, targetRootValue, hl, hb.1, he.2,
          hshape, htype]
    · simp [nodeCheckValue, sourceRootValue, targetRootValue, hl, hb.1, he.2, hshape]
  · apply booleanEquality ht.1 tbool
    rw [ht.2]
    simp [nodeCheckValue, targetRootValue, hl, hb.2, he.1]

theorem opaqueOutput (S T M : Nat → Nat → Nat) (v p : Nat)
    (sbool : S v p = 0 ∨ S v p = 1) (tbool : T v p = 0 ∨ T v p = 1)
    (ha : tagValue v ≠ 2) (hl : tagValue v ≠ 1)
    (hst : S v p = 1 → T v p = 1) :
    validatorValue (sourceRootValue S M) (targetRootValue T) M v p = S v p ∧
    validatorValue (targetRootValue T) (fun _ _ => 1) (fun _ _ => 1) v p = T v p := by
  have hs := actualOriginalHereditaryValidatorRecurrence (sourceRootValue S M) (targetRootValue T) M v p
  have ht := actualOriginalHereditaryValidatorRecurrence (targetRootValue T) (fun _ _ => 1) (fun _ _ => 1) v p
  constructor
  · apply booleanEquality hs.1 sbool
    rw [hs.2]
    simp only [nodeCheckValue, sourceRootValue, targetRootValue, ha, hl, if_false,
      and_true]
    by_cases h : S v p = 1
    · simp [h, hst h]
    · simp [h]
  · apply booleanEquality ht.1 tbool
    rw [ht.2]
    simp [nodeCheckValue, targetRootValue, ha, hl]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityEqualityBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityEqualityBranchProof
