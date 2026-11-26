module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalAcceptanceCalibrationProof NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open TwoSol20261113.CalibratedPrimary.Membership

theorem anyStepEvaluation (E : Program 3) (a rest input parameter : Nat) :
    evaluate (anyStep E) (a ::ᵥ rest ::ᵥ input ::ᵥ parameter ::ᵥ nil) =
      if evaluate E (ofFn ![a,input,parameter]) = 1 then 1 else rest := by
  rw [anyStep,evalBranch,evalNormalize]
  change (if (if evaluate E (ofFn ![a,input,parameter]) = 1 then 1 else 0) = 0
    then rest else 1) = _
  by_cases h : evaluate E (ofFn ![a,input,parameter]) = 1 <;> simp [h]

theorem anyFold (E : Program 3) (xs : List Nat) (input parameter : Nat) :
    xs.foldr (fun a rest => evaluate (anyStep E) (a ::ᵥ rest ::ᵥ input ::ᵥ parameter ::ᵥ nil)) 0 =
      (xs.any (fun a => decide (evaluate E (ofFn ![a,input,parameter]) = 1))).toNat := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.foldr_cons,anyStepEvaluation,ih]
    by_cases h : evaluate E (ofFn ![a,input,parameter]) = 1 <;> simp [h]

theorem anyNative : Targets.AnyNative := by
  intro E reached input parameter
  have h := InternalRawListRecursionEvaluationProof.actualRawListRecursionEvaluation
    2 (InternalAcceptance.constantZero 2) (anyStep E) (input ::ᵥ parameter ::ᵥ nil) reached
  change evaluate (anyEdge E) (ofFn ![reached,input,parameter]) = _ at h
  rw [h]
  exact anyFold E _ input parameter

theorem filterStepEvaluation (E : Program 3) (input rest reached parameter : Nat) :
    evaluate (filterStep E) (input ::ᵥ rest ::ᵥ reached ::ᵥ parameter ::ᵥ nil) =
      if ((decodeNumbers reached).getD []).any
        (fun a => decide (evaluate E (ofFn ![a,input,parameter]) = 1)) then
        1 + Nat.pair input rest else rest := by
  rw [filterStep,evalBranch,evalNormalize]
  change (if (if evaluate (anyEdge E) (ofFn ![reached,input,parameter]) = 1 then 1 else 0) = 0
    then rest else evaluate InternalListCodec.consCode (ofFn ![input,rest])) = _
  rw [anyNative]
  cases hb : ((decodeNumbers reached).getD []).any
    (fun a => decide (evaluate E (ofFn ![a,input,parameter]) = 1)) <;>
    simp [hb,InternalEqualityTestEvaluationProof.vectorTwo,InternalListCodecEvaluationProof.consEvaluation]

theorem filterFold (E : Program 3) (xs : List Nat) (reached parameter : Nat) :
    xs.foldr (fun input rest => evaluate (filterStep E)
      (input ::ᵥ rest ::ᵥ reached ::ᵥ parameter ::ᵥ nil)) 0 =
    numbersNumber (xs.filter (fun input => ((decodeNumbers reached).getD []).any
      (fun a => decide (evaluate E (ofFn ![a,input,parameter]) = 1)))) := by
  induction xs with
  | nil => rfl
  | cons input xs ih =>
    rw [List.foldr_cons,filterStepEvaluation,ih]
    cases hb : ((decodeNumbers reached).getD []).any
      (fun a => decide (evaluate E (ofFn ![a,input,parameter]) = 1)) <;>
      simp [hb,numbersNumber]

theorem filterNative : Targets.FilterNative := by
  intro E pool reached parameter
  have h := InternalRawListRecursionEvaluationProof.actualRawListRecursionEvaluation
    2 (InternalAcceptance.constantZero 2) (filterStep E) (reached ::ᵥ parameter ::ᵥ nil) pool
  change evaluate (filterReached E) (ofFn ![pool,reached,parameter]) = _ at h
  rw [h]
  exact filterFold E _ reached parameter

theorem appendFold (xs ys : List Nat) :
    xs.foldr (fun head rest => 1 + Nat.pair head rest) (numbersNumber ys) = numbersNumber (xs ++ ys) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.foldr_cons,List.cons_append,numbersNumber,ih]

theorem appendEvaluation (prefix : Nat) (ys : List Nat) :
    evaluate InternalApplicationValidityStackAppend.append (ofFn ![prefix,numbersNumber ys]) =
      numbersNumber (((decodeNumbers prefix).getD []) ++ ys) := by
  have h := InternalRawListRecursionEvaluationProof.actualRawListRecursionEvaluation
    1 (.projection 0) InternalApplicationValidityStackAppend.appendStep (numbersNumber ys ::ᵥ nil) prefix
  change evaluate InternalApplicationValidityStackAppend.append (ofFn ![prefix,numbersNumber ys]) = _ at h
  rw [h]
  have hs (head rest : Nat) : evaluate InternalApplicationValidityStackAppend.appendStep
      (head ::ᵥ rest ::ᵥ numbersNumber ys ::ᵥ nil) = 1 + Nat.pair head rest := by
    change evaluate InternalListCodec.consCode (ofFn ![head,rest]) = _
    rw [InternalEqualityTestEvaluationProof.vectorTwo,InternalListCodecEvaluationProof.consEvaluation]
  simp only [hs]
  exact appendFold _ ys

theorem expansionNative : Targets.ExpansionNative := by
  intro E pool reached parameter
  change evaluate InternalApplicationValidityStackAppend.append
    (ofFn ![reached,evaluate (filterReached E) (ofFn ![pool,reached,parameter])]) = _
  rw [filterNative,appendEvaluation]

theorem originalStepCalibration : Targets.OriginalStepCalibration := by
  intro n arity symbols S E parameter hE pool reached
  rw [expansionNative]
  simp only [entriesCode,numbersRoundTrip,Option.getD_some,ContextUniformPrimary.step]
  congr 1
  rw [List.map_append]
  congr 1
  have htest (r : NumberedUniformPackedDecoding.RawPacked n) :
      (reached.map Encodable.encode).any (fun a =>
        decide (evaluate E (ofFn ![a,Encodable.encode r,parameter]) = 1)) =
      reached.any (fun a => NumberedExchangeCode.packedCodeExchange arity symbols S a r) := by
    rw [List.any_map]
    congr 1
    funext a
    rw [hE]
    cases NumberedExchangeCode.packedCodeExchange arity symbols S a r <;> rfl
  induction pool with
  | nil => rfl
  | cons r pool ih =>
    simp only [List.map_cons,List.filter_cons,htest]
    cases hb : reached.any (fun a => NumberedExchangeCode.packedCodeExchange arity symbols S a r) <;>
      simp [hb,ih]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.NativeProof
