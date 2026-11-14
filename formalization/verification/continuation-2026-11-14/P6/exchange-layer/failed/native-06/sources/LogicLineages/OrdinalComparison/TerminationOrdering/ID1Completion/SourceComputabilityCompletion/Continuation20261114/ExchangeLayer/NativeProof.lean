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

theorem input0 (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) :
    (input n arity p).get 0 = p.2.1.1 := rfl

theorem input1 (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) :
    (input n arity p).get 1 = Encodable.encode p.2.1.2.1 := rfl

theorem input2 (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) :
    (input n arity p).get 2 = Encodable.encode p.2.1.2.2.1 := rfl

theorem input3 (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) :
    (input n arity p).get 3 = p.2.1.2.2.2.1 := rfl

theorem input4 (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) :
    (input n arity p).get 4 = Encodable.encode p.2.1.2.2.2.2.1 := rfl

theorem input5 (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) :
    (input n arity p).get 5 = Encodable.encode p.2.1.2.2.2.2.2.1 := rfl

theorem input6 (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) :
    (input n arity p).get 6 = Encodable.encode p.2.1.2.2.2.2.2.2 := rfl

theorem input7 (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) :
    (input n arity p).get 7 = p.2.2.1.1 := rfl

theorem input8 (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) :
    (input n arity p).get 8 = Encodable.encode p.2.2.1.2.1 := rfl

theorem input9 (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) :
    (input n arity p).get 9 = Encodable.encode p.2.2.1.2.2.1 := rfl

theorem input10 (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) :
    (input n arity p).get 10 = p.2.2.1.2.2.2.1 := rfl

theorem input11 (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) :
    (input n arity p).get 11 = Encodable.encode p.2.2.1.2.2.2.2.1 := rfl

theorem input12 (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) :
    (input n arity p).get 12 = Encodable.encode p.2.2.1.2.2.2.2.2.1 := rfl

theorem input13 (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) :
    (input n arity p).get 13 = Encodable.encode p.2.2.1.2.2.2.2.2.2 := rfl

theorem input14 (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) :
    (input n arity p).get 14 = (p.2.2.2.getD 0 false).toNat := rfl

theorem input15 (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) :
    (input n arity p).get 15 = (p.2.2.2.getD 3 false).toNat := rfl

theorem input16 (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) :
    (input n arity p).get 16 = (NumberedExchangeCode.headMove arity p.1.1 p.1.2 p.2.1.2.2.1 p.2.1.2.2.2.2.2.1 p.2.2.1.2.2.1 p.2.2.1.2.2.2.2.2.1).toNat := rfl

theorem input17 (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) :
    (input n arity p).get 17 = Encodable.encode (headResult (decodeHead p.2.1.2.2.1)) := rfl

theorem input18 (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) :
    (input n arity p).get 18 = Encodable.encode (headResult (decodeHead p.2.2.1.2.2.1)) := rfl

theorem zeroEval (v : List.Vector Nat 19) : evaluate (InternalAcceptance.constantZero 19) v = 0 := rfl

theorem nativeLambda (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) :
    evaluate lambdaCase (input n arity p) =
      (decide (p.2.1.2.1 = p.2.2.1.2.1) && p.2.2.2.getD 0 false).toNat := by
  simp only [lambdaCase,bothValue,eqFieldBool,projectionEval]
  simp only [input0,input1,input2,input3,input4,input5,input6,input7,input8,input9,input10,input11,input12,input13,input14,input15,input16,input17,input18]
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
  simp only [applicationCase,bothValue,anyValue,eqFieldBool,projectionEval,input0,input1,input2,input3,input4,input5,input6,input7,input8,input9,input10,input11,input12,input13,input14,input15,input16,input17,input18]
  simp only [boolAnd,boolOr,Encodable.encode_injective.eq_iff]

theorem nativeOrdinary (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) :
    evaluate ordinaryCase (input n arity p) =
      ((NumberedExchangeCode.headMove arity p.1.1 p.1.2 p.2.1.2.2.1 p.2.1.2.2.2.2.2.1
        p.2.2.1.2.2.1 p.2.2.1.2.2.2.2.2.1 &&
        decide (headResult (decodeHead p.2.2.1.2.2.1) = headResult (decodeHead p.2.1.2.2.1))) ||
        (decide (p.2.1.2.2.1 = p.2.2.1.2.2.1) && p.2.2.2.getD 0 false)).toNat := by
  simp only [ordinaryCase,bothValue,anyValue,eqFieldBool,projectionEval,input0,input1,input2,input3,input4,input5,input6,input7,input8,input9,input10,input11,input12,input13,input14,input15,input16,input17,input18]
  simp only [boolAnd,boolOr,Encodable.encode_injective.eq_iff]

theorem decideAnd (P Q : Prop) [Decidable P] [Decidable Q] :
    decide (P ∧ Q) = (decide P && decide Q) := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp,hq]

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
  simp only [numberedCase,bothValue,anyValue,eqFieldBool,projectionEval,input0,input1,input2,input3,input4,input5,input6,input7,input8,input9,input10,input11,input12,input13,input14,input15,input16,input17,input18]
  simp only [boolAnd,boolOr,Encodable.encode_injective.eq_iff,decideAnd,Bool.and_assoc,Bool.or_assoc]

theorem boolIf (P : Prop) [Decidable P] (a b : Bool) :
    (if P then a else b).toNat = if P then a.toNat else b.toNat := by
  by_cases h : P <;> simp only [h,ite_true,ite_false]

theorem dispatchEval (a b c d e : Program 19) (v : List.Vector Nat 19) :
    evaluate (choose (eqField 0 7)
      (choose (tagIs 1) a (choose (tagIs 2) b (choose (tagIs 4) c
        (choose (tagIs 5) d (choose (tagIs 7) e (InternalAcceptance.constantZero 19))))))
      (InternalAcceptance.constantZero 19)) v =
    if v.get 0 = v.get 7 then
      if v.get 0 = 1 then evaluate a v else
      if v.get 0 = 2 then evaluate b v else
      if v.get 0 = 4 then evaluate c v else
      if v.get 0 = 5 then evaluate d v else
      if v.get 0 = 7 then evaluate e v else 0
    else 0 := by
  simp only [chooseValue,eqFieldValue,tagValue,zeroEval]
  split_ifs <;> simp_all

theorem nativeCalibration : Targets.NativeCalibration := by
  intro n arity p
  simp only [layer,dispatchEval,nativeLambda,nativeApplication,nativeOrdinary,nativeNumbered,
    input0,input7,NumberedExchangeCodePrimrecProof.layer,boolIf,Bool.toNat_false]

theorem nativeRecursiveLayer : Targets.NativeRecursiveLayer := by
  intro n arity window source target
  rw [nativeCalibration,NumberedExchangeCodePrimrecProof.layerCalibration]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.NativeProof
