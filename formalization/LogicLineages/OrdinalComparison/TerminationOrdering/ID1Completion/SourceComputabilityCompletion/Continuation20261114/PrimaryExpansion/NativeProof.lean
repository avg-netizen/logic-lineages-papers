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
    by_cases h : evaluate E (ofFn ![a,input,parameter]) = 1 <;>
      simp only [List.any_cons,h,ite_true,ite_false,decide_true,decide_false,Bool.true_or,Bool.false_or,Bool.toNat_true]

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
  have hc : evaluate (.composition (anyEdge E) ![.projection 2,.projection 0,.projection 3])
      (input ::ᵥ rest ::ᵥ reached ::ᵥ parameter ::ᵥ nil) =
      (((decodeNumbers reached).getD []).any
        (fun a => decide (evaluate E (ofFn ![a,input,parameter]) = 1))).toNat :=
    anyNative E reached input parameter
  rw [filterStep,evalBranch,evalNormalize,hc]
  cases hb : ((decodeNumbers reached).getD []).any
    (fun a => decide (evaluate E (ofFn ![a,input,parameter]) = 1))
  · simp only [Bool.toNat_false,Nat.zero_ne_one,ite_false,ite_true,Bool.false_eq_true]
    rfl
  · simp only [Bool.toNat_true,ite_true,Nat.one_ne_zero,ite_false]
    exact InternalListCodecEvaluationProof.consEvaluation input rest

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
      simp only [List.filter_cons,hb,Bool.false_eq_true,ite_false,ite_true,numbersNumber]

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

theorem appendEvaluation (front : Nat) (ys : List Nat) :
    evaluate InternalApplicationValidityStackAppend.append (ofFn ![front,numbersNumber ys]) =
      numbersNumber (((decodeNumbers front).getD []) ++ ys) := by
  have h := InternalRawListRecursionEvaluationProof.actualRawListRecursionEvaluation
    1 (.projection 0) InternalApplicationValidityStackAppend.appendStep (numbersNumber ys ::ᵥ nil) front
  change evaluate InternalApplicationValidityStackAppend.append (ofFn ![front,numbersNumber ys]) = _ at h
  rw [h]
  have hs (head rest : Nat) : evaluate InternalApplicationValidityStackAppend.appendStep
      (head ::ᵥ rest ::ᵥ numbersNumber ys ::ᵥ nil) = 1 + Nat.pair head rest := by
    exact InternalListCodecEvaluationProof.consEvaluation head rest
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
    simp only [Function.comp_def]
    rw [hE]
    cases NumberedExchangeCode.packedCodeExchange arity symbols S a r <;> rfl
  induction pool with
  | nil => rfl
  | cons r pool ih =>
    simp only [List.map_cons,List.filter_cons,htest]
    cases hb : reached.any (fun a => NumberedExchangeCode.packedCodeExchange arity symbols S a r) <;>
      simp only [hb,Bool.false_eq_true,ite_false,ite_true,List.map_cons,ih]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.NativeProof
