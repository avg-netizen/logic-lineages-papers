import LogicLineages.PersistentMarking.NativeOrdinalExponentialTargets

namespace LogicLineages.PersistentMarking.NativeOrdinalStepLambdaTargets
open Spine NativeReduction NativeIndexedCarrierTargets NativeIteratorStrictTargets
open NativeOrdinalBasisTargets NativeOrdinalArithmeticTargets NativeOrdinalExponentialTargets

def StepLambdaBeta (S : Signature) (abstraction result : Expr) (x : ClosedNativeTerm S indexType) : Prop :=
  ∃ source target : ClosedNativeTerm S indexType,
    source.val = app indexType indexType abstraction x.val ∧
    target.val = result ∧ Reduction S source.val target.val ∧ NativeBelow target source

def MultiplicationStepLambdaBeta : Prop :=
  ∀ S (a x : ClosedNativeTerm S indexType),
    StepLambdaBeta S (multiplicationStep a.val) (binaryApplication addition x.val a.val) x

def PowerStepLambdaBeta : Prop :=
  ∀ S (x : ClosedNativeTerm S indexType),
    StepLambdaBeta S powerStep (binaryApplication multiplication x.val omegaCarrier) x

end LogicLineages.PersistentMarking.NativeOrdinalStepLambdaTargets
