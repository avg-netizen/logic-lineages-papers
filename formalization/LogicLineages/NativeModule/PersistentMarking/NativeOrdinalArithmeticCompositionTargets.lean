module

public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalIterationTargets
public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalStepLambdaProof
public import LogicLineages.PersistentMarking.OrdinalArithmeticRealizationTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeOrdinalArithmeticCompositionTargets
open Spine NativeIndexedCarrierTargets NativeIteratorStrictTargets
open NativeOrdinalRealizationTargets NativeOrdinalIterationTargets
open NativeOrdinalBasisTargets NativeOrdinalBasisProof NativeOrdinalArithmeticTargets
open NativeOrdinalArithmeticTypingProof NativeOrdinalExponentialTargets NativeOrdinalExponentialTypingProof
open NativeOrdinalStepLambdaProof OrdinalArithmeticRealizationTargets

def literalArithmetic (S : Signature) : ArithmeticTerms (nativeTerms S) where
  iterator := typedIterator S Base
  zero := ⟨ordinalZero, zeroClosed S⟩
  successor := ⟨ordinalSuccessor, successorClosed S⟩
  addition := ⟨addition, additionClosed S⟩
  multiplication := ⟨multiplication, multiplicationClosed S⟩
  omega := ⟨omegaCarrier, omegaClosed S⟩
  power := ⟨ordinalPower, powerClosed S⟩
  fix := ⟨ordinalFix, fixClosed S⟩
  multiplicationStep a := ⟨multiplicationStep a.val, multiplicationStepClosed S a⟩
  powerStep := ⟨powerStep, powerStepClosed S⟩

def LiteralNativeArithmeticRealizes : Prop :=
  ∀ S, ∃ wf : WellFounded (@NativeBelow S indexType),
    ArithmeticOperationsRealize wf (literalArithmetic S)

end LogicLineages.PersistentMarking.NativeOrdinalArithmeticCompositionTargets
