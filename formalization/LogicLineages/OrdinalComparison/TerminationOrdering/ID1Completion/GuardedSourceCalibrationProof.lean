module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.PositiveTypedCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceCalibrationProof
open Source GuardedSource InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

theorem vectorThree (v : List.Vector Nat 3) :
    List.Vector.ofFn ![v.get 0,v.get 1,v.get 2] = v := by
  apply List.Vector.ext
  intro i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun q => Fin.elim0 q) k) j) i

theorem vectorFour (v : List.Vector Nat 4) :
    List.Vector.ofFn ![v.get 0,v.get 1,v.get 2,v.get 3] = v := by
  apply List.Vector.ext
  intro i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.cases rfl (fun q => Fin.elim0 q) l) k) j) i

theorem evalComposeOne {m : Nat} (f : Program 1) (p : Program m) (v : List.Vector Nat m) :
    evaluate (.composition f ![p]) v = evaluate f (List.Vector.ofFn ![evaluate p v]) := by
  change evaluate f _ = _
  congr 1

theorem evalComposeTwo {m : Nat} (f : Program 2) (p q : Program m) (v : List.Vector Nat m) :
    evaluate (.composition f ![p,q]) v =
      evaluate f (List.Vector.ofFn ![evaluate p v,evaluate q v]) := by
  change evaluate f _ = _
  congr 1

theorem evalComposeThree {m : Nat} (f : Program 3) (p q r : Program m) (v : List.Vector Nat m) :
    evaluate (.composition f ![p,q,r]) v =
      evaluate f (List.Vector.ofFn ![evaluate p v,evaluate q v,evaluate r v]) := by
  change evaluate f _ = _
  congr 1

theorem evalEquality (x y : Nat) :
    evaluate InternalEqualityTest.equalityTest (List.Vector.ofFn ![x,y]) =
      if x = y then 1 else 0 := by
  have hv : List.Vector.ofFn ![x,y] = x ::ᵥ y ::ᵥ List.Vector.nil := by
    apply List.Vector.ext
    intro i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun q => Fin.elim0 q) j) i
  rw [hv]
  exact InternalEqualityTestEvaluationProof.exactEqualityEvaluation x y

theorem evalTypedTag (tag : Program 2) (v : List.Vector Nat 3) :
    evaluate (typedTag tag) v = evaluate tag (List.Vector.ofFn ![v.get 0,v.get 2]) := by
  rw [typedTag,evalComposeTwo]
  rfl

theorem evalTypedMatch (tag : Program 2) (v : List.Vector Nat 3) :
    evaluate (typedMatch tag) v =
      if v.get 1 = evaluate tag (List.Vector.ofFn ![v.get 0,v.get 2]) then 1 else 0 := by
  rw [typedMatch,evalComposeTwo,evalTypedTag,evalEquality]
  rfl

theorem evalLeftTag (tag : Program 2) (v : List.Vector Nat 4) :
    evaluate (leftTag tag) v = evaluate tag (List.Vector.ofFn ![v.get 0,v.get 1]) := by
  rw [leftTag,evalComposeTwo]
  rfl

theorem evalRightTag (tag : Program 2) (v : List.Vector Nat 4) :
    evaluate (rightTag tag) v = evaluate tag (List.Vector.ofFn ![v.get 0,v.get 2]) := by
  rw [rightTag,evalComposeTwo]
  rfl

theorem evalSourceTyped (typed : Program 3) (tag : Program 2) (v : List.Vector Nat 4) :
    evaluate (sourceTyped typed tag) v = evaluate typed (List.Vector.ofFn
      ![v.get 0,evaluate tag (List.Vector.ofFn ![v.get 0,v.get 1]),v.get 1]) := by
  rw [sourceTyped,evalComposeThree,evalLeftTag]
  rfl

theorem evalTargetTyped (typed : Program 3) (tag : Program 2) (v : List.Vector Nat 4) :
    evaluate (targetTyped typed tag) v = evaluate typed (List.Vector.ofFn
      ![v.get 0,evaluate tag (List.Vector.ofFn ![v.get 0,v.get 2]),v.get 2]) := by
  rw [targetTyped,evalComposeThree,evalRightTag]
  rfl

theorem evalSameTag (tag : Program 2) (v : List.Vector Nat 4) :
    evaluate (sameTag tag) v = if
      evaluate tag (List.Vector.ofFn ![v.get 0,v.get 1]) =
        evaluate tag (List.Vector.ofFn ![v.get 0,v.get 2]) then 1 else 0 := by
  rw [sameTag,evalComposeTwo,evalLeftTag,evalRightTag,evalEquality]

theorem evalWindowAt (window : Program 1) (v : List.Vector Nat 4) :
    evaluate (windowAt window) v = evaluate window (List.Vector.ofFn ![v.get 0]) := by
  rw [windowAt,evalComposeOne]
  rfl

theorem actualTypedRange : GuardedSourceTargets.ActualTypedRange := by
  intro n arity v
  have hb (b : Bool) : b.toNat = 0 ∨ b.toNat = 1 := by cases b <;> simp
  have hfixed (Gamma : List Ty) (w : List.Vector Nat 3) :
      OrdinaryArithmeticTypedCarrier.typedValue n arity Gamma w = 0 ∨
      OrdinaryArithmeticTypedCarrier.typedValue n arity Gamma w = 1 := hb _
  cases ho : Encodable.decode (α := ContextUniform.Object) (v.get 2) with
  | none => simp [JointGammaTyped.typedValue,ho]
  | some obj =>
    simpa only [JointGammaTyped.typedValue,ho] using
      hfixed obj.1 (List.Vector.ofFn ![v.get 0,v.get 1,obj.2])

theorem tagCalibration (tag : Program 2)
    (htag : ∀ v, evaluate tag v = GuardCalibration.typeTagValue v) (c x : Nat) :
    evaluate tag (List.Vector.ofFn ![c,x]) = GuardCalibration.typeTag c x := by
  simpa only [GuardCalibration.typeTagValue,List.Vector.get_ofFn,Matrix.cons_val_zero,
    Matrix.cons_val_one] using htag (List.Vector.ofFn ![c,x])

theorem typedCalibration (n : Nat) (arity : Fin n → Nat) (typed : Program 3) (tag : Program 2)
    (htyped : ∀ v, evaluate typed v = JointGammaTyped.typedValue n arity v)
    (htag : ∀ v, evaluate tag v = GuardCalibration.typeTagValue v) (v : List.Vector Nat 3) :
    evaluate (guardedTyped typed tag) v = JointGammaTyped.typedValue n arity v := by
  rw [guardedTyped,actualConjunctionEvaluation,htyped,evalTypedMatch,tagCalibration tag htag]
  rcases actualTypedRange n arity v with hz | ho
  · simp only [hz,Nat.zero_ne_one,false_and,ite_false]
  · have htagv := GuardCalibrationProof.actualTypedTypeTag n arity (v.get 0) (v.get 1) (v.get 2)
        (by simpa only [vectorThree] using ho)
    simp only [ho,htagv,eq_self_iff_true,ite_true,true_and]

theorem positiveCalibration (n : Nat) (arity : Fin n → Nat)
    (positive : Program 4) (typed : Program 3) (tag : Program 2) (window : Program 1)
    (hp : ∀ v, evaluate positive v = ContextUniform.positiveValue n arity v)
    (ht : ∀ v, evaluate typed v = JointGammaTyped.typedValue n arity v)
    (htag : ∀ v, evaluate tag v = GuardCalibration.typeTagValue v)
    (hw : ∀ v, evaluate window v = GuardCalibration.validWindowValue n v)
    (v : List.Vector Nat 4) :
    evaluate (guardedPositive positive typed tag window) v = ContextUniform.positiveValue n arity v := by
  have hwv : evaluate (windowAt window) v = GuardCalibration.validWindow n (v.get 0) := by
    rw [evalWindowAt,hw]
    rfl
  have hsv : evaluate (sourceTyped typed tag) v = JointGammaTyped.typedValue n arity
      (List.Vector.ofFn ![v.get 0,GuardCalibration.typeTag (v.get 0) (v.get 1),v.get 1]) := by
    rw [evalSourceTyped,tagCalibration tag htag,ht]
  have htv : evaluate (targetTyped typed tag) v = JointGammaTyped.typedValue n arity
      (List.Vector.ofFn ![v.get 0,GuardCalibration.typeTag (v.get 0) (v.get 2),v.get 2]) := by
    rw [evalTargetTyped,tagCalibration tag htag,ht]
  have hev : evaluate (sameTag tag) v = if GuardCalibration.typeTag (v.get 0) (v.get 1) =
      GuardCalibration.typeTag (v.get 0) (v.get 2) then 1 else 0 := by
    rw [evalSameTag,tagCalibration tag htag,tagCalibration tag htag]
  rw [guardedPositive,evalBranch,activation,actualConjunctionEvaluation,hwv,hsv,
    acceptedTarget,actualConjunctionEvaluation,actualConjunctionEvaluation,hp,htv,hev]
  by_cases hclosed : GuardCalibration.validWindow n (v.get 0) = 1
  · by_cases hsource : JointGammaTyped.typedValue n arity
        (List.Vector.ofFn ![v.get 0,GuardCalibration.typeTag (v.get 0) (v.get 1),v.get 1]) = 1
    · rcases PositiveTypedCalibrationProof.actualPositiveRange n arity v with hp0 | hp1
      · simp only [hclosed,hsource,hp0,eq_self_iff_true,true_and,false_and,and_true,and_false,ite_true,ite_false,Nat.zero_ne_one,Nat.one_ne_zero]
      · have htarget := PositiveTypedCalibrationProof.actualTypedSuccessor n arity (v.get 0)
          (GuardCalibration.typeTag (v.get 0) (v.get 1)) (v.get 1) (v.get 2) (v.get 3)
          hclosed hsource (by simpa only [vectorFour] using hp1)
        have he := GuardCalibrationProof.actualTypedTypeTag n arity (v.get 0)
          (GuardCalibration.typeTag (v.get 0) (v.get 1)) (v.get 2) htarget
        simp only [he,hclosed,hsource,hp1,htarget,eq_self_iff_true,true_and,false_and,and_true,and_false,ite_true,ite_false,Nat.zero_ne_one,Nat.one_ne_zero]
    · simp only [hclosed,hsource,eq_self_iff_true,true_and,false_and,and_true,and_false,ite_true,ite_false,Nat.zero_ne_one,Nat.one_ne_zero]
  · simp only [hclosed,eq_self_iff_true,true_and,false_and,and_true,and_false,ite_true,ite_false,Nat.zero_ne_one,Nat.one_ne_zero]

theorem actualGuardedCalibration : GuardedSourceTargets.ActualGuardedCalibration := by
  intro n arity oldSource oldComp tag window hs hc ht hw
  constructor
  · exact ⟨hs.1,hs.2.1,positiveCalibration n arity oldSource.positive oldComp.typed tag window
      hs.2.2.1 hc.1 ht hw,hs.2.2.2⟩
  · exact ⟨typedCalibration n arity oldComp.typed tag hc.1 ht,hc.2⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceCalibrationProof
