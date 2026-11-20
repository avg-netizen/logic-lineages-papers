import LogicLineages.PersistentMarking.NativeOrdinalRealizationTargets
import LogicLineages.PersistentMarking.NativeOrdinalArithmeticTypingProof
import LogicLineages.PersistentMarking.OrdinalArithmeticOrbitTargets

namespace LogicLineages.PersistentMarking.NativeOrdinalArithmeticRealizationTargets
open NativeIndexedCarrierTargets NativeIteratorStrictTargets NativeOrdinalBasisTargets
open NativeOrdinalBasisProof NativeOrdinalArithmeticTargets NativeOrdinalArithmeticTypingProof
open OrdinalRealizationTargets OrdinalArithmeticOrbitTargets NativeOrdinalRealizationTargets

def NativeOrdinalArithmeticRealization : Prop :=
  ∀ S, ∃ wf : WellFounded (@NativeBelow S indexType),
    ∃ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
      (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal),
      OrdinalArithmeticEquations Z s add mul ∧
      Realizes (nativeTerms S) wf .base ⟨ordinalZero, zeroClosed S⟩ Z ∧
      Realizes (nativeTerms S) wf (.arrow .base .base) ⟨ordinalSuccessor, successorClosed S⟩ s ∧
      Realizes (nativeTerms S) wf (.arrow .base (.arrow .base .base)) ⟨addition, additionClosed S⟩ add ∧
      Realizes (nativeTerms S) wf (.arrow .base (.arrow .base .base)) ⟨multiplication, multiplicationClosed S⟩ mul

end LogicLineages.PersistentMarking.NativeOrdinalArithmeticRealizationTargets
