module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalApplicationCertificateConstructors InternalPairingEvaluationProof InternalUnpairEvaluationProof
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo)

theorem pairOfEvaluation {n : Nat} (p q : Program n) (v : List.Vector Nat n) :
    evaluate (pairOf p q) v = Nat.pair (evaluate p v) (evaluate q v) := by
  change evaluate InternalPairing.pairing
    (List.Vector.ofFn fun i : Fin 2 => evaluate (![p,q] i) v) = _
  rw [vectorTwo]
  exact exactPairingEvaluation _ _

theorem leftOfEvaluation {n : Nat} (p : Program n) (v : List.Vector Nat n) :
    evaluate (leftOf p) v = (Nat.unpair (evaluate p v)).1 := by
  change evaluate InternalUnpair.left (List.Vector.ofFn fun _ : Fin 1 => evaluate p v) = _
  rw [vectorOne]
  exact (exactUnpairEvaluation _).1

theorem rightOfEvaluation {n : Nat} (p : Program n) (v : List.Vector Nat n) :
    evaluate (rightOf p) v = (Nat.unpair (evaluate p v)).2 := by
  change evaluate InternalUnpair.right (List.Vector.ofFn fun _ : Fin 1 => evaluate p v) = _
  rw [vectorOne]
  exact (exactUnpairEvaluation _).2

theorem consOfEvaluation {n : Nat} (p q : Program n) (v : List.Vector Nat n) :
    evaluate (consOf p q) v = 1 + Nat.pair (evaluate p v) (evaluate q v) := by
  change evaluate InternalListCodec.consCode
    (List.Vector.ofFn fun i : Fin 2 => evaluate (![p,q] i) v) = _
  rw [vectorTwo]
  exact InternalListCodecEvaluationProof.consEvaluation _ _

theorem twoEvaluation (n : Nat) (v : List.Vector Nat n) : evaluate (two n) v = 2 := rfl

theorem oneVector (v : List.Vector Nat 1) : v = v.get 0 ::ᵥ List.Vector.nil := by
  apply List.Vector.ext
  intro i
  obtain rfl : i = 0 := Fin.eq_zero i
  simp

theorem leftEvaluation (v : List.Vector Nat 1) :
    evaluate InternalUnpair.left v = (Nat.unpair (v.get 0)).1 := by
  rw [oneVector v]
  exact (exactUnpairEvaluation _).1

theorem rightEvaluation (v : List.Vector Nat 1) :
    evaluate InternalUnpair.right v = (Nat.unpair (v.get 0)).2 := by
  rw [oneVector v]
  exact (exactUnpairEvaluation _).2

theorem packedApplicationEvaluation (v : List.Vector Nat 4) :
    evaluate packedApplication v =
      Nat.pair (v.get 1) (Nat.pair 2 (Nat.pair (v.get 0) (Nat.pair (v.get 2) (v.get 3)))) := by
  unfold packedApplication
  rw [pairOfEvaluation,pairOfEvaluation,pairOfEvaluation,pairOfEvaluation,twoEvaluation]
  rfl

theorem applicationEvaluation (v : List.Vector Nat 4) :
    evaluate application v = ApplicationCertificateLift.applicationValue v := by
  change evaluate packedApplication (List.Vector.ofFn fun i : Fin 4 =>
    evaluate ((![Program.projection 0,.projection 1,rightOf (.projection 2),
      rightOf (.projection 3)] : Fin 4 → Program 4) i) v) = _
  rw [packedApplicationEvaluation]
  change Nat.pair (v.get 1) (Nat.pair 2 (Nat.pair (v.get 0)
    (Nat.pair (evaluate (rightOf (.projection 2)) v) (evaluate (rightOf (.projection 3)) v)))) = _
  rw [rightOfEvaluation,rightOfEvaluation]
  rfl

theorem stepLiftEvaluation (v : List.Vector Nat 1) :
    evaluate stepLift v = ApplicationCertificateLift.stepValue v := by
  unfold stepLift prefixedPath
  rw [pairOfEvaluation,consOfEvaluation,twoEvaluation,leftEvaluation,rightEvaluation]
  rfl

theorem edgeCodeEvaluation (v : List.Vector Nat 3) :
    evaluate edgeCode v =
      NumberedNumericQuotientEdge.edgeCertificateNumber (v.get 0) (v.get 1) (v.get 2) := by
  unfold edgeCode
  rw [pairOfEvaluation,pairOfEvaluation]
  rfl

theorem selectorsEvaluation (v : List.Vector Nat 1) :
    evaluate source v = ApplicationCertificateLiftEdge.sourceOf (v.get 0) ∧
    evaluate target v = ApplicationCertificateLiftEdge.targetOf (v.get 0) ∧
    evaluate step v = ApplicationCertificateLiftEdge.stepOf (v.get 0) := by
  refine ⟨leftEvaluation v,?_,?_⟩
  · unfold target
    rw [leftOfEvaluation,rightEvaluation]
    rfl
  · unfold step
    rw [rightOfEvaluation,rightEvaluation]
    rfl

theorem certificateFieldEvaluation (p : Program 1) (v : List.Vector Nat 4) :
    evaluate (certificateField p) v = evaluate p (v.get 3 ::ᵥ List.Vector.nil) := by
  change evaluate p (List.Vector.ofFn fun _ : Fin 1 => v.get 3) = _
  rw [vectorOne]

theorem fieldApplicationEvaluation (p : Program 1) (v : List.Vector Nat 4) :
    evaluate (.composition application
      ![.projection 0,.projection 1,certificateField p,.projection 2]) v =
    ApplicationCertificateLift.rawApplication (v.get 0) (v.get 1)
      (evaluate p (v.get 3 ::ᵥ List.Vector.nil)) (v.get 2) := by
  change evaluate application (List.Vector.ofFn fun i : Fin 4 =>
    evaluate ((![Program.projection 0,.projection 1,certificateField p,
      .projection 2] : Fin 4 → Program 4) i) v) = _
  rw [applicationEvaluation]
  change ApplicationCertificateLift.rawApplication (v.get 0) (v.get 1)
    (evaluate (certificateField p) v) (v.get 2) = _
  rw [certificateFieldEvaluation]

theorem sourceApplicationEvaluation (v : List.Vector Nat 4) :
    evaluate sourceApplication v = ApplicationCertificateLift.rawApplication (v.get 0) (v.get 1)
      (ApplicationCertificateLiftEdge.sourceOf (v.get 3)) (v.get 2) := by
  rw [sourceApplication,fieldApplicationEvaluation,(selectorsEvaluation _).1]
  rfl

theorem targetApplicationEvaluation (v : List.Vector Nat 4) :
    evaluate targetApplication v = ApplicationCertificateLift.rawApplication (v.get 0) (v.get 1)
      (ApplicationCertificateLiftEdge.targetOf (v.get 3)) (v.get 2) := by
  rw [targetApplication,fieldApplicationEvaluation,(selectorsEvaluation _).2.1]
  rfl

theorem liftedStepEvaluation (v : List.Vector Nat 4) :
    evaluate liftedStep v = ApplicationCertificateLift.liftStep
      (ApplicationCertificateLiftEdge.stepOf (v.get 3)) := by
  change evaluate stepLift (List.Vector.ofFn fun _ : Fin 1 => evaluate (certificateField step) v) = _
  rw [stepLiftEvaluation]
  change ApplicationCertificateLift.liftStep (evaluate (certificateField step) v) = _
  rw [certificateFieldEvaluation,(selectorsEvaluation _).2.2]
  rfl

theorem edgeLiftEvaluation (v : List.Vector Nat 4) :
    evaluate edgeLift v = ApplicationCertificateLiftEdge.edgeValue v := by
  change evaluate edgeCode (List.Vector.ofFn fun i : Fin 3 =>
    evaluate (![sourceApplication,targetApplication,liftedStep] i) v) = _
  rw [edgeCodeEvaluation]
  change NumberedNumericQuotientEdge.edgeCertificateNumber
    (evaluate sourceApplication v) (evaluate targetApplication v) (evaluate liftedStep v) = _
  rw [sourceApplicationEvaluation,targetApplicationEvaluation,liftedStepEvaluation]
  rfl

theorem exactOriginalCalibration : InternalApplicationCertificateConstructorsTargets.ExactOriginalCalibration :=
  ⟨packedApplicationEvaluation,applicationEvaluation,stepLiftEvaluation,edgeCodeEvaluation,
    selectorsEvaluation,edgeLiftEvaluation⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsEvaluationProof
