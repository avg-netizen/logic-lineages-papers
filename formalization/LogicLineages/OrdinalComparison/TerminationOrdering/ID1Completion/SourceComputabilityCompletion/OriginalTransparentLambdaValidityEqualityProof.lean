module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityEqualityNumericProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityParameterProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityValidatorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceNormalizedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceRootProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityEqualityProof
open OriginalHereditaryValidity OriginalTransparentLambdaValidity
open InternalOriginalUniformDescentSelection (Data Calibrated)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The normalized captured leaves retain exactly the original numeric source,
target and membership functions. No finite-window closure is used. -/
theorem calibratedNumericEquality (n : Nat) (arity : Fin n → Nat) (rawData : Data)
    (hc : Calibrated n arity rawData) (value parameter : Nat) :
    sourceValidatorValue rawData value parameter =
      InternalOriginalUniformParameterLeaves.sourceValue n arity (List.Vector.ofFn ![value,parameter]) ∧
    targetValidatorValue rawData value parameter =
      InternalOriginalUniformParameterLeaves.targetValue n arity (List.Vector.ofFn ![value,parameter]) := by
  let S := fun v p => InternalOriginalUniformParameterLeaves.sourceValue n arity (List.Vector.ofFn ![v,p])
  let T := fun v p => InternalOriginalUniformParameterLeaves.targetValue n arity (List.Vector.ofFn ![v,p])
  let M := fun v p => InternalOriginalUniformParameterLeaves.memberValue n (List.Vector.ofFn ![v,p])
  have hn := OriginalHereditaryValidityRecurrenceSourceNormalizedProof.normalizedCalibration n arity rawData hc
  have hs : binaryValue (normalizedData rawData).oldSource = S := by
    funext v p
    exact hn.1 _
  have ht : binaryValue (normalizedData rawData).oldTarget = T := by
    funext v p
    exact hn.2.1 _
  have hm : binaryValue (normalizedData rawData).member = M := by
    funext v p
    exact hn.2.2.2 _
  change validatorValue (sourceRootValue (binaryValue (normalizedData rawData).oldSource)
      (binaryValue (normalizedData rawData).member))
      (targetRootValue (binaryValue (normalizedData rawData).oldTarget))
      (binaryValue (normalizedData rawData).member) value parameter = S value parameter ∧
    validatorValue (targetRootValue (binaryValue (normalizedData rawData).oldTarget))
      (fun _ _ => 1) (fun _ _ => 1) value parameter = T value parameter
  rw [hs,ht,hm]
  exact OriginalTransparentLambdaValidityEqualityNumericProof.transparentNumericEquality S T M
    (fun v p => OriginalHereditaryValidityRecurrenceSourceRootProof.sourceBoolean n arity _)
    (fun v p => OriginalTransparentLambdaValidityParameterProof.targetBoolean n arity _)
    (fun v p => OriginalTransparentLambdaValidityParameterProof.sourceImpliesTarget n arity v p)
    (fun v p h => OriginalTransparentLambdaValidityApplicationProof.actualOriginalTransparentApplicationEquations n arity v p h)
    (fun v p h => OriginalTransparentLambdaValidityLambdaProof.actualOriginalTransparentLambdaEquations n arity v p h)
    value parameter

theorem actualOriginalTransparentSourceEquality :
    OriginalTransparentLambdaValidityTargets.ActualOriginalTransparentSourceEquality := by
  intro n arity rawData hc v
  have hv : v = List.Vector.ofFn ![v.get 0,v.get 1] := List.Vector.ext fun i => by
    refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i <;> rfl
  calc
    evaluate (sourceValidator rawData) v = sourceValidatorValue rawData (v.get 0) (v.get 1) :=
      (OriginalTransparentLambdaValidityValidatorProof.actualOriginalTransparentValidatorCalibration rawData v).1
    _ = InternalOriginalUniformParameterLeaves.sourceValue n arity (List.Vector.ofFn ![v.get 0,v.get 1]) :=
      (calibratedNumericEquality n arity rawData hc (v.get 0) (v.get 1)).1
    _ = evaluate rawData.oldSource v := by rw [hc.1, ← hv]

theorem actualOriginalTransparentTargetEquality :
    OriginalTransparentLambdaValidityTargets.ActualOriginalTransparentTargetEquality := by
  intro n arity rawData hc v
  have hv : v = List.Vector.ofFn ![v.get 0,v.get 1] := List.Vector.ext fun i => by
    refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i <;> rfl
  calc
    evaluate (targetValidator rawData) v = targetValidatorValue rawData (v.get 0) (v.get 1) :=
      (OriginalTransparentLambdaValidityValidatorProof.actualOriginalTransparentValidatorCalibration rawData v).2
    _ = InternalOriginalUniformParameterLeaves.targetValue n arity (List.Vector.ofFn ![v.get 0,v.get 1]) :=
      (calibratedNumericEquality n arity rawData hc (v.get 0) (v.get 1)).2
    _ = evaluate rawData.oldTarget v := by rw [hc.2.1, ← hv]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityEqualityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityEqualityProof
