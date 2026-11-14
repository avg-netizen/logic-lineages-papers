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

theorem nativeCalibration : Targets.NativeCalibration := by
  intro n arity p
  simp only [layer,chooseValue,eqFieldValue,tagValue,lambdaCase,applicationCase,ordinaryCase,
    numberedCase,bothValue,anyValue,evaluate,input,List.Vector.get_ofFn,Matrix.cons_val_zero,
    Matrix.cons_val_succ,NumberedExchangeCodePrimrecProof.layer,Encodable.encode_injective.eq_iff]
  split_ifs <;> simp_all

theorem nativeRecursiveLayer : Targets.NativeRecursiveLayer := by
  intro n arity window source target
  rw [nativeCalibration,NumberedExchangeCodePrimrecProof.layerCalibration]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.NativeProof
