import LogicLineages.PersistentMarking.NativeOrdinalBasisTargets
import LogicLineages.PersistentMarking.NativeClosedBetaChecks
import LogicLineages.PersistentMarking.NativeIndexedTypingThinProof
import LogicLineages.PersistentMarking.NativeCarrierThinChecks
import LogicLineages.PersistentMarking.ClosedSyntaxProof

namespace LogicLineages.PersistentMarking.NativeOrdinalBasisProof
open Spine NameBridge NativeReduction NativeTypingProof
open NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIteratorStrictTargets NativeClosedApplication NativeOrdinalBasisTargets

theorem zeroClosed (S : Signature) : ClosedNative S ordinalZero indexType :=
  ⟨⟨⟨.lam (.bound rfl), True.intro⟩, True.intro, fun _ => rfl⟩,
    fun _ _ => by simp [ordinalZero, DecisionInventory.heads]⟩

private theorem selectorClosed (S : Signature) :
    ClosedNative S (left indexType ordinalZero) (.arrow indexType indexType) :=
  NativeIndexedTypingThinProof.leftClosed S indexType ordinalZero (zeroClosed S)

theorem successorClosed (S : Signature) : ClosedNative S ordinalSuccessor (.arrow indexType indexType) := by
  have selector := selectorClosed S
  have fnTyped := ClosingProof.weakening (left indexType ordinalZero) (.arrow indexType indexType)
    selector.1.1.1 (EmptyContext.push indexType)
  have bodyTyped : Typed (EmptyContext.push indexType) ordinalSuccessorBody indexType :=
    .head (.cons fnTyped (.cons (.bound rfl) .nil))
  have bodyValid : Valid S ordinalSuccessorBody := ⟨⟨0, rfl⟩, selector.1.1.2, True.intro, True.intro⟩
  have bodyOrdinary : Ordinary ordinalSuccessorBody := ⟨selector.1.2.1, True.intro, True.intro⟩
  refine ⟨⟨⟨.lam bodyTyped, bodyValid⟩, bodyOrdinary, ?_⟩, ?_⟩
  · intro name
    simp [ordinalSuccessor, ordinalSuccessorBody, app, freeOccurs, freeOccursArgs, selector.1.2.2 name]
  · intro name arity
    simp [ordinalSuccessor, ordinalSuccessorBody, app, DecisionInventory.heads,
      DecisionInventory.headsArgs, selector.2 name arity]

theorem closedBasis : ClosedOrdinalBasis := by
  intro S
  exact ⟨zeroClosed S, successorClosed S,
    NativeClosedProof.carrier S indexType ordinalSuccessor ordinalZero (successorClosed S) (zeroClosed S)⟩

private theorem instanceEquation (S : Signature) (a : Expr) :
    substitute (.cons a .nil) 0 ordinalSuccessorBody = successorInstance a := by
  have fnSubstitution := ClosedSyntaxProof.closedSubstitute (left indexType ordinalZero)
    (.arrow indexType indexType) (selectorClosed S).1.1.1 (.cons a .nil)
  simp only [ordinalSuccessorBody, successorInstance, app, substitute, substituteArgs, fnSubstitution,
    Nat.lt_irrefl, if_false, Nat.sub_zero, Args.get, SubstitutionProof.shiftZero]

theorem successorSteps : OrdinalSuccessorSteps := by
  intro S a
  have hSuccessor := successorClosed S
  obtain ⟨midpoint, betaValue, reduction, strictBeta⟩ :=
    NativeClosedBetaChecks.exact_ClosedNativeBeta S indexType indexType ordinalSuccessorBody hSuccessor a
  have midpointValue := betaValue.trans (instanceEquation S a.val)
  have hFn := selectorClosed S
  have hBody : ClosedNative S (successorInstance a.val) indexType :=
    NativeClosedProof.application S indexType indexType _ _ hFn a.property
  have argumentEdge : ConfinedPair.Strict S (successorInstance a.val) a.val :=
    ⟨⟨indexType, hBody.1.1, a.property.1.1, hBody.1.2.1, a.property.1.2.1⟩,
      .intro hBody.1.1 a.property.1.1 rfl
        (secondSelect S indexType indexType (left indexType ordinalZero) a.val .nil
          hFn.1.1 a.property.1.1 a.property.1.2.1 .nil True.intro),
      rightIncluded indexType indexType (left indexType ordinalZero) a.val⟩
  refine ⟨applyClosed ⟨ordinalSuccessor, hSuccessor⟩ a, midpoint, rfl, midpointValue, reduction, strictBeta, ?_⟩
  change ConfinedPair.Strict S midpoint.val a.val
  rw [midpointValue]
  exact argumentEdge

theorem capFinite : CapAboveFiniteApplications := by
  intro S B P U n
  have reflexive := ElementaryProof.ordinaryReflexive S P.val (.arrow B B) P.property.1.1 P.property.1.2.1
  obtain ⟨base, absorb⟩ := NativeCarrierThinChecks.exact_Carrier S B P.val P.val U.val
    P.property P.property U.property reflexive (fun _ h => h)
  refine ⟨rfl, ?_⟩
  induction n with
  | zero => exact base
  | succ n ih =>
    let prev := finiteApplication P U n
    have prior : ConfinedPair.Strict S (W B P.val U.val) prev.val := ih
    exact absorb prev.val prev.property.1 prior.2.2 prior

end LogicLineages.PersistentMarking.NativeOrdinalBasisProof
