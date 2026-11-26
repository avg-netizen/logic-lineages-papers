import LogicLineages.PersistentMarking.NativeOrdinalArithmeticCompositionTargets
import LogicLineages.PersistentMarking.NativeOrdinalIterationProof
import LogicLineages.PersistentMarking.NativeOrdinalBasisChecks
import LogicLineages.PersistentMarking.NativeOrdinalArithmeticChecks
import LogicLineages.PersistentMarking.NativeOrdinalExponentialChecks
import LogicLineages.PersistentMarking.NativeOrdinalStepLambdaChecks
import LogicLineages.PersistentMarking.OrdinalArithmeticRealizationProof

namespace LogicLineages.PersistentMarking.NativeOrdinalArithmeticCompositionProof
open Spine NativeIndexedCarrierTargets NativeIteratorStrictTargets
open NativeOrdinalBasisTargets NativeOrdinalArithmeticTargets NativeOrdinalExponentialTargets
open NativeOrdinalRealizationTargets NativeOrdinalRealizationProof NativeOrdinalIterationProof
open OrdinalNativeOrbitProof OrdinalArithmeticRealizationTargets OrdinalArithmeticRealizationProof
open NativeOrdinalArithmeticCompositionTargets

private theorem alignEdge {S : Signature}
    {source target p q : ClosedNativeTerm S indexType}
    (hp : p.val = source.val) (hq : q.val = target.val) (edge : NativeBelow q p) :
    NativeBelow target source := by
  have sourceEq : p = source := Subtype.ext hp
  have targetEq : q = target := Subtype.ext hq
  simpa only [sourceEq, targetEq] using edge

private theorem alignPath {S : Signature}
    {source target p middle q : ClosedNativeTerm S indexType}
    (hp : p.val = source.val) (hq : q.val = target.val)
    (first : NativeBelow middle p) (second : NativeBelow q middle) :
    TwoStrictEdges (terms := nativeTerms S) source target :=
  ⟨middle, alignEdge hp rfl first, alignEdge rfl hq second⟩

private theorem literalEdges (S : Signature) : ArithmeticStrictEdges (literalArithmetic S) := by
  let op := literalArithmetic S
  change ArithmeticStrictEdges op
  constructor
  · intro a
    obtain ⟨start, middle, source, _, _, first, second⟩ :=
      NativeOrdinalBasisChecks.exact_OrdinalSuccessorSteps S a
    exact alignPath (source := applyUnary op.successor a) (target := a) source rfl first second
  · intro a b
    obtain ⟨start, middle, result, source, _, target, _, _, first, second⟩ :=
      NativeOrdinalArithmeticChecks.exact_OrdinalAdditionBeta S a b
    exact alignPath (source := applyBinary op.addition a b) (target := applyIterator op b op.successor a)
      source target first second
  · intro a x
    obtain ⟨start, result, source, target, _, edge⟩ :=
      NativeOrdinalStepLambdaChecks.exact_MultiplicationStepLambdaBeta S a x
    exact alignEdge (source := applyUnary (op.multiplicationStep a) x) (target := applyBinary op.addition x a)
      source target edge
  · intro a b
    obtain ⟨start, middle, result, source, _, target, _, _, first, second⟩ :=
      NativeOrdinalArithmeticChecks.exact_OrdinalMultiplicationBeta S a b
    exact alignPath (source := applyBinary op.multiplication a b)
      (target := applyIterator op b (op.multiplicationStep a) op.zero) source target first second
  · intro n
    have finiteValues (k : Nat) : finiteSuccessor op k = finiteApplication op.successor op.zero k := by
      induction k with
      | zero => rfl
      | succ k ih => exact congrArg (applyUnary op.successor) ih
    have carrier : cap op.successor op.zero = op.omega := Subtype.ext rfl
    change NativeBelow (finiteSuccessor op n) op.omega
    rw [finiteValues n, ← carrier]
    exact (NativeOrdinalBasisChecks.exact_CapAboveFiniteApplications S indexType op.successor op.zero n).2
  · intro x
    obtain ⟨start, result, source, target, _, edge⟩ :=
      NativeOrdinalStepLambdaChecks.exact_PowerStepLambdaBeta S x
    exact alignEdge (source := applyUnary op.powerStep x) (target := applyBinary op.multiplication x op.omega)
      source target edge
  · intro a
    obtain ⟨start, result, source, target, _, edge⟩ :=
      NativeOrdinalExponentialChecks.exact_NativeOrdinalPowerBeta S a
    exact alignEdge (source := applyUnary op.power a)
      (target := applyIterator op a op.powerStep (literalOne op)) source target edge
  · intro f z
    obtain ⟨start, middle, result, source, _, target, _, _, first, second⟩ :=
      NativeOrdinalExponentialChecks.exact_NativeOrdinalFixBeta S f z
    exact alignPath (source := applyUnary ((nativeTerms S).app OrdinalFunction OrdinalFunction op.fix f) z)
      (target := applyIterator op op.omega f (applyUnary op.successor z)) source target first second

private theorem iteratorRealizes (S : Signature) (wf : WellFounded (@NativeBelow S indexType)) :
    IteratorRealizesOrbit wf (literalArithmetic S) := by
  obtain ⟨_, realization⟩ := exact_NativeIteratorRealizesFullPrefix S
  obtain ⟨value, equations, realized⟩ := realization Base
  have canonical : value = fun β f x => orbit Base f x β := by
    funext β f x
    exact congrFun ((exact_FullPrefixOrbitExists Base f x).unique (equations f x)
      (orbitEquations Base f x)) β
  rw [canonical] at realized
  exact realized

theorem exact_LiteralNativeArithmeticRealizes : LiteralNativeArithmeticRealizes := by
  intro S
  let wf := NativeClosedStrictWellFoundedChecks.exact_ClosedNativeStrictWellFounded S indexType
  exact ⟨wf, exact_ArithmeticRealizationComposition (nativeTerms S) wf (literalArithmetic S)
    (applicationEdge S) (literalEdges S) (iteratorRealizes S wf)⟩

#print axioms exact_LiteralNativeArithmeticRealizes

end LogicLineages.PersistentMarking.NativeOrdinalArithmeticCompositionProof
