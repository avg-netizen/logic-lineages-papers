module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TypedPrimaryEdge.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.NativeProof
open Source Source.SourceMarkedSyntax NumberedAuxiliaryCoding NumberedAuxiliaryDecoding
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem constantValue (k : Nat) (v : List.Vector Nat 19) : evaluate (constant k) v = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change Nat.succ (evaluate (constant k) v) = k+1
    rw [ih]

theorem eqFieldValue (i j : Fin 19) (v : List.Vector Nat 19) :
    evaluate (eqField i j) v = if v.get i = v.get j then 1 else 0 := by
  change evaluate InternalEqualityTest.equalityTest (List.Vector.ofFn ![v.get i,v.get j]) = _
  rw [InternalEqualityTestEvaluationProof.vectorTwo]
  exact InternalEqualityTestEvaluationProof.exactEqualityEvaluation _ _

theorem tagValue (k : Nat) (v : List.Vector Nat 19) :
    evaluate (tagIs k) v = if v.get 0 = k then 1 else 0 := by
  change evaluate InternalEqualityTest.equalityTest (List.Vector.ofFn ![v.get 0,evaluate (constant k) v]) = _
  rw [constantValue,InternalEqualityTestEvaluationProof.vectorTwo]
  exact InternalEqualityTestEvaluationProof.exactEqualityEvaluation _ _

theorem bothValue (p q : Program 19) (v : List.Vector Nat 19) :
    evaluate (both p q) v = if evaluate p v = 1 ∧ evaluate q v = 1 then 1 else 0 :=
  InternalAcceptanceCalibrationProof.actualConjunctionEvaluation 19 p q v

theorem anyValue (p q : Program 19) (v : List.Vector Nat 19) :
    evaluate (any p q) v = if evaluate p v = 1 ∨ evaluate q v = 1 then 1 else 0 := by
  rw [any,InternalAcceptanceCalibrationProof.evalBranch]
  simp only [InternalAcceptanceCalibrationProof.evalNormalize]
  by_cases hp : evaluate p v = 1 <;> by_cases hq : evaluate q v = 1 <;> simp [hp,hq]

theorem chooseValue (p yes no : Program 19) (v : List.Vector Nat 19) :
    evaluate (choose p yes no) v = if evaluate p v = 0 then evaluate no v else evaluate yes v :=
  InternalAcceptanceCalibrationProof.evalBranch p no yes v

theorem boolAnd (a b : Bool) :
    (if a.toNat = 1 ∧ b.toNat = 1 then 1 else 0) = (a && b).toNat := by
  cases a <;> cases b <;> rfl

theorem boolOr (a b : Bool) :
    (if a.toNat = 1 ∨ b.toNat = 1 then 1 else 0) = (a || b).toNat := by
  cases a <;> cases b <;> rfl

theorem eqFieldBool (i j : Fin 19) (v : List.Vector Nat 19) :
    evaluate (eqField i j) v = (decide (v.get i = v.get j)).toNat := by
  rw [eqFieldValue]
  by_cases h : v.get i = v.get j <;> simp [h]

theorem projectionEval (i : Fin 19) (v : List.Vector Nat 19) : evaluate (.projection i) v = v.get i := rfl

theorem lambdaEval (v : List.Vector Nat 19) :
    evaluate lambdaCase v = if v.get 1 = v.get 8 ∧ v.get 14 = 1 then 1 else 0 := by
  simp only [lambdaCase,bothValue,eqFieldValue,projectionEval]
  by_cases h : v.get 1 = v.get 8 <;> simp [h]

theorem nativeLambda (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) :
    evaluate lambdaCase (input n arity p) =
      (decide (p.2.1.2.1 = p.2.2.1.2.1) && p.2.2.2.getD 0 false).toNat := by
  simp only [lambdaCase,bothValue,eqFieldBool,projectionEval]
  simp only [input,List.Vector.get_ofFn]
  change (if (decide (Encodable.encode p.2.1.2.1 = Encodable.encode p.2.2.1.2.1)).toNat = 1 ∧
    (p.2.2.2.getD 0 false).toNat = 1 then 1 else 0) = _
  rw [boolAnd]
  simp only [Encodable.encode_injective.eq_iff]

theorem nativeApplication (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) :
    evaluate applicationCase (input n arity p) =
      (decide (p.2.1.2.1 = p.2.2.1.2.1) &&
        ((decide (p.2.1.2.2.2.2.2.2 = p.2.2.1.2.2.2.2.2.2) && p.2.2.2.getD 0 false) ||
         (decide (p.2.1.2.2.2.2.2.1 = p.2.2.1.2.2.2.2.2.1) && p.2.2.2.getD 3 false))).toNat := by
  simp only [applicationCase,bothValue,anyValue,eqFieldBool,projectionEval,input,List.Vector.get_ofFn]
  simp only [boolAnd,boolOr,Encodable.encode_injective.eq_iff]

theorem nativeOrdinary (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) :
    evaluate ordinaryCase (input n arity p) =
      ((NumberedExchangeCode.headMove arity p.1.1 p.1.2 p.2.1.2.2.1 p.2.1.2.2.2.2.2.1
        p.2.2.1.2.2.1 p.2.2.1.2.2.2.2.2.1 &&
        decide (headResult (decodeHead p.2.2.1.2.2.1) = headResult (decodeHead p.2.1.2.2.1))) ||
        (decide (p.2.1.2.2.1 = p.2.2.1.2.2.1) && p.2.2.2.getD 0 false)).toNat := by
  simp only [ordinaryCase,bothValue,anyValue,eqFieldBool,projectionEval,input,List.Vector.get_ofFn]
  simp only [boolAnd,boolOr,Encodable.encode_injective.eq_iff]

theorem nativeNumbered (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) :
    evaluate numberedCase (input n arity p) =
      (decide (p.2.1.2.2.2.1 = p.2.2.1.2.2.2.1 ∧ p.2.1.2.1 = p.2.2.1.2.1 ∧
        p.2.1.2.2.2.2.1 = p.2.2.1.2.2.2.2.1) &&
        ((decide (p.2.1.2.2.2.2.2.2 = p.2.2.1.2.2.2.2.2.2) &&
          NumberedExchangeCode.headMove arity p.1.1 p.1.2 p.2.1.2.2.1 p.2.1.2.2.2.2.2.1
            p.2.2.1.2.2.1 p.2.2.1.2.2.2.2.2.1) ||
        (decide (p.2.1.2.2.1 = p.2.2.1.2.2.1 ∧ p.2.1.2.2.2.2.2.2 = p.2.2.1.2.2.2.2.2.2) && p.2.2.2.getD 0 false) ||
        (decide (p.2.1.2.2.1 = p.2.2.1.2.2.1 ∧ p.2.1.2.2.2.2.2.1 = p.2.2.1.2.2.2.2.2.1) && p.2.2.2.getD 3 false))).toNat := by
  simp only [numberedCase,bothValue,anyValue,eqFieldBool,projectionEval,input,List.Vector.get_ofFn]
  simp only [boolAnd,boolOr,Encodable.encode_injective.eq_iff,decide_and]

theorem nativeCalibration : Targets.NativeCalibration := by
  intro n arity p
  simp only [layer,chooseValue,eqFieldValue,tagValue,nativeLambda,nativeApplication,nativeOrdinary,nativeNumbered,
    NumberedExchangeCodePrimrecProof.layer]
  simp only [input,List.Vector.get_ofFn]
  change (if (if p.2.1.1 = p.2.2.1.1 then 1 else 0) = 0 then 0 else _) = _
  split_ifs <;> simp_all

theorem nativeRecursiveLayer : Targets.NativeRecursiveLayer := by
  intro n arity window source target
  rw [nativeCalibration,NumberedExchangeCodePrimrecProof.layerCalibration]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.NativeProof
